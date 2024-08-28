// Super Mario 64 PC Port's audio asset extractor and converter, translated from mixed
// Python, Make and C to C++

// g++ -o extract_sounds extract_sounds.cpp -std=c++20 -laudiofile -Wall -Wextra
// cp /path/to/baserom.us.z64 baserom.us.z64
// ./extract_sounds
// US ROM only
// first, it extracts all necessary sound/sequences/us/*.m64 and sound/samples/*/*.aiff files
// then, converts all sound/samples/*/*.aiff files to sound/samples/*/*.table files // TODO: rest of the
// .table files for all the extended soundbank
// TODO:
// then, converts all sound/samples/*/*.aiff and sound/samples/*/*.table files to sound/samples/*/*.aifc
// files then, converts the sound/samples/ and sound/sound_banks/ folders into two out of the four
// "game-ready" sound asset files that load.c requires, sound/sound_data.ctl and
// sound/sound_data.tbl then, converts the sound/sequences.json file and the sound/sequences/ and
// sound/sound_banks/ folders into the remaining two "game-ready" sound asset files, sound/sequences.bin
// and sound/bank_sets

#include <chrono>
#include <filesystem>
#include <fstream>
#include <iostream>
#include <map>
#include <set>
#include <sstream>
#include <string>
#include <tuple>
#include <unordered_map>
#include <vector>
#include <regex>

#include <cassert>
#include <cmath>
#include <cstring>

#include <audiofile.h>

using namespace std;
namespace fs = filesystem;

// Asset maps containing purely address information of where the files are in the ROM relative
// to various reference points that are calculated within the extraction logic below them
// and associates those addresses with the filenames and folder structure chosen by the decompilation
// team and adjusted by later teams for cross-platform ports
map<const string, const vector<uint32_t>> sequence_map = {
    { "sound/sequences/us/01_cutscene_collect_star.m64", { 619, 8076816 } },
    { "sound/sequences/us/02_menu_title_screen.m64", { 8254, 8077440 } },
    { "sound/sequences/us/03_level_grass.m64", { 5122, 8085696 } },
    { "sound/sequences/us/04_level_inside_castle.m64", { 2494, 8090832 } },
    { "sound/sequences/us/05_level_water.m64", { 4780, 8093328 } },
    { "sound/sequences/us/06_level_hot.m64", { 2451, 8098112 } },
    { "sound/sequences/us/07_level_boss_koopa.m64", { 3418, 8100576 } },
    { "sound/sequences/us/08_level_snow.m64", { 8143, 8104000 } },
    { "sound/sequences/us/09_level_slide.m64", { 7432, 8112144 } },
    { "sound/sequences/us/0A_level_spooky.m64", { 5674, 8119584 } },
    { "sound/sequences/us/0B_event_piranha_plant.m64", { 1395, 8125264 } },
    { "sound/sequences/us/0C_level_underground.m64", { 4887, 8126672 } },
    { "sound/sequences/us/0D_menu_star_select.m64", { 134, 8131568 } },
    { "sound/sequences/us/0E_event_powerup.m64", { 3129, 8131712 } },
    { "sound/sequences/us/0F_event_metal_cap.m64", { 2770, 8134848 } },
    { "sound/sequences/us/10_event_koopa_message.m64", { 552, 8137632 } },
    { "sound/sequences/us/11_level_koopa_road.m64", { 4741, 8138192 } },
    { "sound/sequences/us/12_event_high_score.m64", { 271, 8142944 } },
    { "sound/sequences/us/13_event_merry_go_round.m64", { 1657, 8143216 } },
    { "sound/sequences/us/14_event_race.m64", { 197, 8144880 } },
    { "sound/sequences/us/15_cutscene_star_spawn.m64", { 644, 8145088 } },
    { "sound/sequences/us/16_event_boss.m64", { 3435, 8145744 } },
    { "sound/sequences/us/17_cutscene_collect_key.m64", { 671, 8149184 } },
    { "sound/sequences/us/18_event_endless_stairs.m64", { 1777, 8149856 } },
    { "sound/sequences/us/19_level_boss_koopa_final.m64", { 3515, 8151648 } },
    { "sound/sequences/us/1A_cutscene_credits.m64", { 14313, 8155168 } },
    { "sound/sequences/us/1B_event_solve_puzzle.m64", { 216, 8169488 } },
    { "sound/sequences/us/1C_event_toad_message.m64", { 208, 8169712 } },
    { "sound/sequences/us/1D_event_peach_message.m64", { 432, 8169920 } },
    { "sound/sequences/us/1E_cutscene_intro.m64", { 1764, 8170352 } },
    { "sound/sequences/us/1F_cutscene_victory.m64", { 2058, 8172128 } },
    { "sound/sequences/us/20_cutscene_ending.m64", { 1882, 8174192 } },
    { "sound/sequences/us/21_menu_file_select.m64", { 781, 8176080 } },
    { "sound/sequences/us/22_cutscene_lakitu.m64", { 313, 8176864 } },
};

map<const string, const vector<uint32_t>> seqfile_map = {
    { "ctl", { 97856, 5748512 } },
    { "tbl", { 2216704, 5846368 } },
};

// I made a new map of the .aiff filenames to the ROM addresses that I think is better. previously the
// only information conveyed by the asset map was a convoluted index of what order the assets were in.
// That caused a problem for me because some samples are shared between multiple sample banks, causing
// the order to easily become scrambled when the address arrays aren't constantly sorted in the
// particular way the Python version does it. The resulting bug manifesting was many .aiff files being
// written to the wrong filenames. I changed it to actual addresses into the ROM marking the data
// relevant to parsing that specific .aiff file from the ROM, which is exactly how the asset map for the
// .m64 files already was. This acts as a unique identifier solely used to assign the correct filename,
// eliminating the need for any sorting. I can't use exact sample size as a unique identifier because
// there are indeed a few samples with the exact same length. Maybe it would be better to calculate an
// md5sum hash of some part of each sample to identify it, but I choose to follow the example used by
// the .m64 section. The start of the data specific to each aiff file is calculated based on an offset
// from the ctl[1] value in the seqfile_map right above this, 5748512, so each of these addresses is
// relative to that address, 5748512.
map<const uint32_t, const string> sample_map = {
    { 352, "sound/samples/sfx_1/00_twirl.aiff" },
    { 480, "sound/samples/sfx_1/01_brushing.aiff" },
    { 640, "sound/samples/sfx_1/02_hand_touch.aiff" },
    { 768, "sound/samples/sfx_1/03_yoshi.aiff" },
    { 896, "sound/samples/sfx_1/04_plop.aiff" },
    { 1024, "sound/samples/sfx_1/05_heavy_landing.aiff" },
    { 1424, "sound/samples/sfx_terrain/00_step_default.aiff" },
    { 1552, "sound/samples/sfx_terrain/01_step_grass.aiff" },
    { 1680, "sound/samples/sfx_terrain/02_step_stone.aiff" },
    { 1808, "sound/samples/sfx_terrain/03_step_spooky.aiff" },
    { 1936, "sound/samples/sfx_terrain/04_step_snow.aiff" },
    { 2064, "sound/samples/sfx_terrain/05_step_ice.aiff" },
    { 2192, "sound/samples/sfx_terrain/06_step_metal.aiff" },
    { 2320, "sound/samples/sfx_terrain/07_step_sand.aiff" },
    { 2768, "sound/samples/sfx_water/00_plunge.aiff" },
    { 2896, "sound/samples/sfx_water/01_splash.aiff" },
    { 3024, "sound/samples/sfx_water/02_swim.aiff" },
    { 3360, "sound/samples/sfx_4/00.aiff" },
    { 3520, "sound/samples/sfx_4/01.aiff" },
    { 3680, "sound/samples/sfx_4/02.aiff" },
    { 3840, "sound/samples/sfx_4/03.aiff" },
    { 4000, "sound/samples/sfx_4/04.aiff" },
    { 4160, "sound/samples/sfx_4/05.aiff" },
    { 4320, "sound/samples/sfx_4/06.aiff" },
    { 4480, "sound/samples/sfx_4/07.aiff" },
    { 4640, "sound/samples/sfx_4/08.aiff" },
    { 4800, "sound/samples/sfx_4/09.aiff" },
    { 5392, "sound/samples/sfx_5/00.aiff" },
    { 5520, "sound/samples/sfx_5/01.aiff" },
    { 5648, "sound/samples/sfx_5/02.aiff" },
    { 5776, "sound/samples/sfx_5/03.aiff" },
    { 5904, "sound/samples/sfx_5/04.aiff" },
    { 6032, "sound/samples/sfx_5/05.aiff" },
    { 6160, "sound/samples/sfx_5/06.aiff" },
    { 6288, "sound/samples/sfx_5/07.aiff" },
    { 6416, "sound/samples/sfx_5/08.aiff" },
    { 6544, "sound/samples/sfx_5/09.aiff" },
    { 6672, "sound/samples/sfx_5/0A.aiff" },
    { 6800, "sound/samples/sfx_5/0B.aiff" },
    { 6928, "sound/samples/sfx_5/0C.aiff" },
    { 7056, "sound/samples/sfx_5/0D.aiff" },
    { 7952, "sound/samples/sfx_5/0E.aiff" },
    { 8080, "sound/samples/sfx_5/0F.aiff" },
    { 8240, "sound/samples/sfx_5/10.aiff" },
    { 8400, "sound/samples/sfx_5/11.aiff" },
    { 8688, "sound/samples/sfx_5/12.aiff" },
    { 8816, "sound/samples/sfx_5/13.aiff" },
    { 8976, "sound/samples/sfx_5/14.aiff" },
    { 9104, "sound/samples/sfx_5/15.aiff" },
    { 9232, "sound/samples/sfx_5/16.aiff" },
    { 9360, "sound/samples/sfx_5/17.aiff" },
    { 9488, "sound/samples/sfx_5/18.aiff" },
    { 9616, "sound/samples/sfx_5/19.aiff" },
    { 9776, "sound/samples/sfx_5/1A.aiff" },
    { 9936, "sound/samples/sfx_5/1B.aiff" },
    { 10064, "sound/samples/sfx_5/1C.aiff" },
    { 10864, "sound/samples/sfx_6/00.aiff" },
    { 10992, "sound/samples/sfx_6/01.aiff" },
    { 11120, "sound/samples/sfx_6/02.aiff" },
    { 11248, "sound/samples/sfx_6/03.aiff" },
    { 11376, "sound/samples/sfx_6/04.aiff" },
    { 11504, "sound/samples/sfx_6/05.aiff" },
    { 11632, "sound/samples/sfx_6/06.aiff" },
    { 11760, "sound/samples/sfx_6/07.aiff" },
    { 11888, "sound/samples/sfx_6/08.aiff" },
    { 12016, "sound/samples/sfx_6/09.aiff" },
    { 12176, "sound/samples/sfx_6/0A.aiff" },
    { 12336, "sound/samples/sfx_6/0B.aiff" },
    { 12464, "sound/samples/sfx_6/0C.aiff" },
    { 12592, "sound/samples/sfx_6/0D.aiff" },
    { 13440, "sound/samples/sfx_7/00.aiff" },
    { 13568, "sound/samples/sfx_7/01.aiff" },
    { 13696, "sound/samples/sfx_7/02.aiff" },
    { 13824, "sound/samples/sfx_7/03.aiff" },
    { 13952, "sound/samples/sfx_7/04.aiff" },
    { 14112, "sound/samples/sfx_7/05.aiff" },
    { 14272, "sound/samples/sfx_7/06.aiff" },
    { 14400, "sound/samples/sfx_7/07.aiff" },
    { 14528, "sound/samples/sfx_7/08.aiff" },
    { 14656, "sound/samples/sfx_7/09.aiff" },
    { 14784, "sound/samples/sfx_7/0A.aiff" },
    { 14912, "sound/samples/sfx_7/0B.aiff" },
    { 15040, "sound/samples/sfx_7/0C.aiff" },
    { 15168, "sound/samples/sfx_7/0D_chain_chomp_bark.aiff" },
    { 15968, "sound/samples/sfx_mario/00_mario_jump_hoo.aiff" },
    { 16096, "sound/samples/sfx_mario/01_mario_jump_wah.aiff" },
    { 16224, "sound/samples/sfx_mario/02_mario_yah.aiff" },
    { 16352, "sound/samples/sfx_mario/03_mario_haha.aiff" },
    { 16480, "sound/samples/sfx_mario/04_mario_yahoo.aiff" },
    { 16608, "sound/samples/sfx_mario/05_mario_uh.aiff" },
    { 16736, "sound/samples/sfx_mario/06_mario_hrmm.aiff" },
    { 16864, "sound/samples/sfx_mario/07_mario_wah2.aiff" },
    { 16992, "sound/samples/sfx_mario/08_mario_whoa.aiff" },
    { 17120, "sound/samples/sfx_mario/09_mario_eeuh.aiff" },
    { 17248, "sound/samples/sfx_mario/0A_mario_attacked.aiff" },
    { 17376, "sound/samples/sfx_mario/0B_mario_ooof.aiff" },
    { 17504, "sound/samples/sfx_mario/0C_mario_here_we_go.aiff" },
    { 17632, "sound/samples/sfx_mario/0D_mario_yawning.aiff" },
    { 17760, "sound/samples/sfx_mario/0E_mario_snoring1.aiff" },
    { 17888, "sound/samples/sfx_mario/0F_mario_snoring2.aiff" },
    { 18016, "sound/samples/sfx_mario/10_mario_doh.aiff" },
    { 18144, "sound/samples/sfx_mario/11_mario_game_over.aiff" },
    { 18272, "sound/samples/sfx_mario/12_mario_hello.aiff" },
    { 18400, "sound/samples/sfx_mario/13_mario_press_start_to_play.aiff" },
    { 18528, "sound/samples/sfx_mario/14_mario_twirl_bounce.aiff" },
    { 18656, "sound/samples/sfx_mario/15_mario_snoring3.aiff" },
    { 18784, "sound/samples/sfx_mario/16_mario_so_longa_bowser.aiff" },
    { 18912, "sound/samples/sfx_mario/17_mario_ima_tired.aiff" },
    { 19040, "sound/samples/sfx_mario/18_mario_waha.aiff" },
    { 19168, "sound/samples/sfx_mario/19_mario_yippee.aiff" },
    { 19296, "sound/samples/sfx_mario/1A_mario_lets_a_go.aiff" },
    { 20352, "sound/samples/sfx_9/00.aiff" },
    { 20480, "sound/samples/sfx_9/01.aiff" },
    { 20608, "sound/samples/sfx_9/02.aiff" },
    { 20768, "sound/samples/sfx_9/03.aiff" },
    { 20928, "sound/samples/sfx_9/04_camera_buzz.aiff" },
    { 21056, "sound/samples/sfx_9/05_camera_shutter.aiff" },
    { 21184, "sound/samples/sfx_9/06.aiff" },
    { 21760, "sound/samples/sfx_mario_peach/00_mario_waaaooow.aiff" },
    { 21888, "sound/samples/sfx_mario_peach/01_mario_hoohoo.aiff" },
    { 22016, "sound/samples/sfx_mario_peach/02_mario_panting.aiff" },
    { 22144, "sound/samples/sfx_mario_peach/03_mario_dying.aiff" },
    { 22272, "sound/samples/sfx_mario_peach/04_mario_on_fire.aiff" },
    { 22400, "sound/samples/sfx_mario_peach/05_mario_uh2.aiff" },
    { 22528, "sound/samples/sfx_mario_peach/06_mario_coughing.aiff" },
    { 22656, "sound/samples/sfx_mario_peach/07_mario_its_a_me_mario.aiff" },
    { 22784, "sound/samples/sfx_mario_peach/08_mario_punch_yah.aiff" },
    { 22912, "sound/samples/sfx_mario_peach/09_mario_punch_hoo.aiff" },
    { 23040, "sound/samples/sfx_mario_peach/0A_mario_mama_mia.aiff" },
    { 23168, "sound/samples/sfx_mario_peach/0B_mario_okey_dokey.aiff" },
    { 23296, "sound/samples/sfx_mario_peach/0C_mario_drowning.aiff" },
    { 23424, "sound/samples/sfx_mario_peach/0D_mario_thank_you_playing_my_game.aiff" },
    { 23552, "sound/samples/sfx_mario_peach/0E_peach_dear_mario.aiff" },
    { 23680, "sound/samples/sfx_mario_peach/0F_peach_mario.aiff" },
    { 23808, "sound/samples/sfx_mario_peach/10_peach_power_of_the_stars.aiff" },
    { 23936, "sound/samples/sfx_mario_peach/11_peach_thanks_to_you.aiff" },
    { 24064, "sound/samples/sfx_mario_peach/12_peach_thank_you_mario.aiff" },
    { 24192, "sound/samples/sfx_mario_peach/13_peach_something_special.aiff" },
    { 24320, "sound/samples/sfx_mario_peach/14_peach_bake_a_cake.aiff" },
    { 24448, "sound/samples/sfx_mario_peach/15_peach_for_mario.aiff" },
    { 24576, "sound/samples/sfx_mario_peach/16_peach_mario2.aiff" },
    { 31968, "sound/samples/instruments/00.aiff" },
    { 32128, "sound/samples/instruments/01_banjo_1.aiff" },
    { 32288, "sound/samples/instruments/02.aiff" },
    { 32448, "sound/samples/instruments/03_human_whistle.aiff" },
    { 55184, "sound/samples/instruments/04_bright_piano.aiff" },
    { 59040, "sound/samples/instruments/05_acoustic_bass.aiff" },
    { 55504, "sound/samples/instruments/06_kick_drum_1.aiff" },
    { 55632, "sound/samples/instruments/07_rimshot.aiff" },
    { 55760, "sound/samples/instruments/08.aiff" },
    { 55888, "sound/samples/instruments/09.aiff" },
    { 28400, "sound/samples/instruments/0A_tambourine.aiff" },
    { 51184, "sound/samples/instruments/0B.aiff" },
    { 51312, "sound/samples/instruments/0C_conga_stick.aiff" },
    { 51440, "sound/samples/instruments/0D_clave.aiff" },
    { 26304, "sound/samples/instruments/0E_hihat_closed.aiff" },
    { 34080, "sound/samples/instruments/0F_hihat_open.aiff" },
    { 28912, "sound/samples/instruments/10_cymbal_bell.aiff" },
    { 29040, "sound/samples/instruments/11_splash_cymbal.aiff" },
    { 34464, "sound/samples/instruments/12_snare_drum_1.aiff" },
    { 45056, "sound/samples/instruments/13_snare_drum_2.aiff" },
    { 73456, "sound/samples/instruments/14_strings_5.aiff" },
    { 73616, "sound/samples/instruments/15_strings_4.aiff" },
    { 73296, "sound/samples/instruments/16_french_horns.aiff" },
    { 72976, "sound/samples/instruments/17_trumpet.aiff" },
    { 70688, "sound/samples/instruments/18_timpani.aiff" },
    { 42912, "sound/samples/instruments/19_brass.aiff" },
    { 43072, "sound/samples/instruments/1A_slap_bass.aiff" },
    { 43232, "sound/samples/instruments/1B_organ_2.aiff" },
    { 43392, "sound/samples/instruments/1C.aiff" },
    { 54352, "sound/samples/instruments/1D.aiff" },
    { 29424, "sound/samples/instruments/1E_closed_triangle.aiff" },
    { 29552, "sound/samples/instruments/1F_open_triangle.aiff" },
    { 29680, "sound/samples/instruments/20_cabasa.aiff" },
    { 27568, "sound/samples/instruments/21_sine_bass.aiff" },
    { 38368, "sound/samples/instruments/22_boys_choir.aiff" },
    { 36544, "sound/samples/instruments/23_strings_1.aiff" },
    { 36704, "sound/samples/instruments/24_strings_2.aiff" },
    { 36864, "sound/samples/instruments/25_strings_3.aiff" },
    { 37440, "sound/samples/instruments/26_crystal_rhodes.aiff" },
    { 80880, "sound/samples/instruments/27_harpsichord.aiff" },
    { 38528, "sound/samples/instruments/28_sitar_1.aiff" },
    { 48608, "sound/samples/instruments/29_orchestra_hit.aiff" },
    { 37984, "sound/samples/instruments/2A.aiff" },
    { 38112, "sound/samples/instruments/2B.aiff" },
    { 38240, "sound/samples/instruments/2C.aiff" },
    { 37280, "sound/samples/instruments/2D_trombone.aiff" },
    { 25984, "sound/samples/instruments/2E_accordion.aiff" },
    { 26560, "sound/samples/instruments/2F_sleigh_bells.aiff" },
    { 47520, "sound/samples/instruments/30_rarefaction-lahna.aiff" },
    { 47680, "sound/samples/instruments/31_rarefaction-convolution.aiff" },
    { 47840, "sound/samples/instruments/32_metal_rimshot.aiff" },
    { 47968, "sound/samples/instruments/33_kick_drum_2.aiff" },
    { 48736, "sound/samples/instruments/34_alto_flute.aiff" },
    { 42624, "sound/samples/instruments/35_gospel_organ.aiff" },
    { 63680, "sound/samples/instruments/36_sawtooth_synth.aiff" },
    { 63840, "sound/samples/instruments/37_square_synth.aiff" },
    { 66048, "sound/samples/instruments/38_electric_kick_drum.aiff" },
    { 38688, "sound/samples/instruments/39_sitar_2.aiff" },
    { 53920, "sound/samples/instruments/3A_music_box.aiff" },
    { 25536, "sound/samples/instruments/3B_banjo_2.aiff" },
    { 25696, "sound/samples/instruments/3C_acoustic_guitar.aiff" },
    { 25856, "sound/samples/instruments/3D.aiff" },
    { 39104, "sound/samples/instruments/3E_monk_choir.aiff" },
    { 39264, "sound/samples/instruments/3F.aiff" },
    { 39392, "sound/samples/instruments/40_bell.aiff" },
    { 88912, "sound/samples/instruments/41_pan_flute.aiff" },
    { 29808, "sound/samples/instruments/42_vibraphone.aiff" },
    { 92160, "sound/samples/instruments/43_harmonica.aiff" },
    { 92768, "sound/samples/instruments/44_grand_piano.aiff" },
    { 93088, "sound/samples/instruments/45_french_horns_lq.aiff" },
    { 37024, "sound/samples/instruments/46_pizzicato_strings_1.aiff" },
    { 37152, "sound/samples/instruments/47_pizzicato_strings_2.aiff" },
    { 42784, "sound/samples/instruments/48_steel_drum.aiff" },
    { 79280, "sound/samples/piranha_music_box/00_music_box.aiff" },
    { 58288, "sound/samples/course_start/00_la.aiff" },
    { 80064, "sound/samples/bowser_organ/00_organ_1.aiff" },
    { 80224, "sound/samples/bowser_organ/01_organ_1_lq.aiff" },
    { 90416, "sound/samples/bowser_organ/02_boys_choir.aiff" },
};

const uint16_t TYPE_CTL = 1;
const uint16_t TYPE_TBL = 2;
// End asset map

// Utilities
#define READ_16_BITS(bytes, addr)                                                                      \
    ((static_cast<uint8_t>(bytes[addr]) << 8) | static_cast<uint8_t>(bytes[addr + 1]))

#define READ_32_BITS(bytes, addr)                                                                      \
    ((static_cast<uint8_t>(bytes[addr]) << 24) | (static_cast<uint8_t>(bytes[addr + 1]) << 16)         \
     | (static_cast<uint8_t>(bytes[addr + 2]) << 8) | static_cast<uint8_t>(bytes[addr + 3]))

#define WRITE_16_BITS(val, destbytes, addr)                                                            \
    {                                                                                                  \
        destbytes[addr] = static_cast<byte>((val >> 8) & 0xFF);                                        \
        destbytes[addr + 1] = static_cast<byte>(val & 0xFF);                                           \
    }

#define WRITE_32_BITS(val, destbytes, addr)                                                            \
    {                                                                                                  \
        destbytes[addr] = static_cast<byte>((val >> 24) & 0xFF);                                       \
        destbytes[addr + 1] = static_cast<byte>((val >> 16) & 0xFF);                                   \
        destbytes[addr + 2] = static_cast<byte>((val >> 8) & 0xFF);                                    \
        destbytes[addr + 3] = static_cast<byte>(val & 0xFF);                                           \
    }

#define INTO_BYTES ([](char c) { return static_cast<byte>(c); })

size_t align(const size_t size, const size_t alignment) {
    return static_cast<size_t>((static_cast<int>(size) + (static_cast<int>(alignment) - 1))
                               & -static_cast<int>(alignment));
}

vector<byte> pstring(const string &data_string) {
    uint32_t length = data_string.size();
    vector<byte> data(length + 1);
    data[0] = static_cast<byte>(length);
    transform(data_string.begin(), data_string.end(), data.begin() + 1, INTO_BYTES);
    if (!(length % 2)) {
        data.push_back(static_cast<byte>('\0'));
    }
    return data;
}

vector<byte> serialize_f80(const double num) {
    uint64_t f64 = bit_cast<uint64_t>(num);
    uint64_t f64_sign_bit = f64 & (1ULL << 63);
    vector<byte> result(10, static_cast<byte>(0));

    if (num == 0.0) {
        if (f64_sign_bit) {
            result[0] = static_cast<byte>(0x80);
        }
        return result;
    }

    uint64_t exponent = (f64 & 0x7FF0000000000000) >> 52;
    uint64_t mantissa = f64 & 0xFFFFFFFFFFFFF;

    exponent -= 1023; // IEEE 754 exponent bias for double

    uint16_t sign_exponent = static_cast<uint16_t>((f64_sign_bit >> 48) | (exponent + 0x3FFF));
    uint64_t f80_mantissa = (1ULL << 63) | (mantissa << (63 - 52));

    WRITE_16_BITS(sign_exponent, result, 0);
    for (size_t i = 0; i < 8; ++i) {
        result[2 + i] = static_cast<byte>((f80_mantissa >> (56 - 8 * i)) & 0xFF);
    }

    return result;
}

// aifc_decode.c translated into C++
/**
 * Bruteforcing decoder for converting ADPCM-encoded AIFC into AIFF, in a way
 * that roundtrips with vadpcm_enc.
 */

typedef signed char s8;
typedef short s16;
typedef int s32;
typedef unsigned char u8;
typedef unsigned short u16;
typedef unsigned int u32;
typedef unsigned long long u64;
typedef float f32;

#if __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
#define bswap16(x) (x)
#define bswap32(x) (x)
#define BSWAP16(x)
#define BSWAP32(x)
#define BSWAP16_MANY(x, n)
#else
#define bswap16(x) __builtin_bswap16(x)
#define bswap32(x) __builtin_bswap32(x)
#define BSWAP16(x) x = __builtin_bswap16(x)
#define BSWAP32(x) x = __builtin_bswap32(x)
#define BSWAP16_MANY(x, n)                                                                             \
    for (s32 _i = 0; _i < n; _i++)                                                                     \
    BSWAP16((x)[_i])
#endif

#define NORETURN __attribute__((noreturn))
#define UNUSED __attribute__((unused))

typedef struct {
    u32 ckID, ckSize;
} ChunkHeader;

typedef struct {
    u32 ckID, ckSize, formType;
} Chunk;

typedef struct {
    s16 numChannels;
    u16 numFramesH, numFramesL;
    s16 sampleSize, sampleRate[5]; // 80-bit float
    u16 compressionTypeH, compressionTypeL;
} CommonChunk;

typedef struct {
    s16 MarkerID;
    u16 positionH, positionL;
} Marker;

typedef struct {
    s16 playMode, beginLoop, endLoop;
} DecodeLoop;

typedef struct {
    s8 baseNote, detune, lowNote, highNote, lowVelocity, highVelocity;
    s16 gain;
    DecodeLoop sustainLoop, releaseLoop;
} InstrumentChunk;

typedef struct {
    s32 offset, blockSize;
} SoundDataChunk;

typedef struct {
    s16 version, order, nEntries;
} CodeChunk;

// Shared class declaration
class ALADPCMLoop {
  public:
    uint32_t start, end, count;
    vector<int16_t> state;

    ALADPCMLoop(const uint32_t start, const uint32_t end, const uint32_t count,
                const vector<int16_t> &state);
    ALADPCMLoop(const ALADPCMLoop &l);
    ALADPCMLoop(const uint32_t addr, const vector<byte> &bank_data);
    ALADPCMLoop() = default;

    ALADPCMLoop &operator=(const ALADPCMLoop &loop) = default;
};
// End shared class declaration

size_t read_bytes_from_vec(void *ptr, size_t size, size_t count, const vector<byte> &buffer,
                           size_t *offset) {
    size_t bytes_to_read = size * count;
    size_t bytes_available = buffer.size() - *offset;

    if (bytes_to_read > bytes_available) {
        bytes_to_read = bytes_available;
    }

    memcpy(ptr, buffer.data() + *offset, bytes_to_read);
    *offset += bytes_to_read;

    return bytes_to_read / size;
}

size_t write_bytes_to_vec(const void *ptr, size_t size, size_t count, vector<byte> &buffer,
                          size_t *offset) {
    size_t bytes_to_write = size * count;
    size_t bytes_available = buffer.size() - *offset;

    if (bytes_to_write > bytes_available) {
        buffer.resize(*offset + bytes_to_write);
    }

    memcpy(buffer.data() + *offset, ptr, bytes_to_write);
    *offset += bytes_to_write;

    return bytes_to_write / size;
}

s32 myrand() {
    static u64 state = 1619236481962341ULL;
    state *= 3123692312231ULL;
    state++;
    return state >> 33;
}

s16 qsample(s32 x, s32 scale) {
    // Compute x / 2^scale rounded to the nearest integer, breaking ties towards zero.
    if (scale == 0) {
        return x;
    }
    return (x + (1 << (scale - 1)) - (x > 0)) >> scale;
}

s16 clamp_to_s16(s32 x) {
    if (x < -0x8000) {
        return -0x8000;
    }
    if (x > 0x7fff) {
        return 0x7fff;
    }
    return (s16) x;
}

s32 toi4(s32 x) {
    if (x >= 8) {
        return x - 16;
    }
    return x;
}

s32 read_aifc_codebook(const vector<byte> &aifcData, size_t *fhandle,
                       vector<vector<vector<s32>>> &table, s16 *order, s16 *npredictors) {
    read_bytes_from_vec(order, sizeof(s16), 1, aifcData, fhandle);
    BSWAP16(*order);
    read_bytes_from_vec(npredictors, sizeof(s16), 1, aifcData, fhandle);
    BSWAP16(*npredictors);
    table.resize(*npredictors * sizeof(s32 **));
    for (s32 i = 0; i < *npredictors; i++) {
        table[i].resize(8 * sizeof(s32 *));
        for (s32 j = 0; j < 8; j++) {
            table[i][j].resize((*order + 8) * sizeof(s32));
        }
    }

    for (s32 i = 0; i < *npredictors; i++) {
        vector<vector<s32>> *table_entry = &table[i];
        for (s32 j = 0; j < *order; j++) {
            for (s32 k = 0; k < 8; k++) {
                s16 ts;
                read_bytes_from_vec(&ts, sizeof(s16), 1, aifcData, fhandle);
                BSWAP16(ts);
                (*table_entry)[k][j] = ts;
            }
        }

        for (s32 k = 1; k < 8; k++) {
            (*table_entry)[k][*order] = (*table_entry)[k - 1][*order - 1];
        }

        (*table_entry)[0][*order] = 1 << 11;

        for (s32 k = 1; k < 8; k++) {
            s32 j = 0;
            for (; j < k; j++) {
                (*table_entry)[j][k + *order] = 0;
            }

            for (; j < 8; j++) {
                (*table_entry)[j][k + *order] = (*table_entry)[j - k][*order];
            }
        }
    }
    return 0;
}

vector<ALADPCMLoop> read_loop_points(const vector<byte> &aifcData, size_t *ifile, s16 *nloops) {
    read_bytes_from_vec(nloops, sizeof(s16), 1, aifcData, ifile);
    BSWAP16(*nloops);
    vector<ALADPCMLoop> al(*nloops);
    for (auto &loop : al) {
        loop.state.resize(16);
        read_bytes_from_vec(&loop.start, sizeof(loop.start), 1, aifcData, ifile);
        read_bytes_from_vec(&loop.end, sizeof(loop.end), 1, aifcData, ifile);
        read_bytes_from_vec(&loop.count, sizeof(loop.count), 1, aifcData, ifile);
        read_bytes_from_vec(loop.state.data(), sizeof(*(loop.state.data())), 16, aifcData, ifile);
        BSWAP32(loop.start);
        BSWAP32(loop.end);
        BSWAP32(loop.count);
        BSWAP16_MANY(loop.state, 16);
    }
    return al;
}

s32 inner_product(s32 length, const vector<s32> &v1, s32 *v2) {
    s32 out = 0;
    for (s32 i = 0; i < length; i++) {
        out += v1[i] * v2[i];
    }

    // Compute "out / 2^11", rounded down.
    s32 dout = out / (1 << 11);
    s32 fiout = dout * (1 << 11);
    return dout - (out - fiout < 0);
}

void my_decodeframe(u8 *frame, s32 *state, s32 order, const vector<vector<vector<s32>>> &coefTable) {
    s32 ix[16];

    u8 header = frame[0];
    s32 scale = 1 << (header >> 4);
    s32 optimalp = header & 0xf;

    for (s32 i = 0; i < 16; i += 2) {
        u8 c = frame[1 + i / 2];
        ix[i] = c >> 4;
        ix[i + 1] = c & 0xf;
    }

    for (s32 i = 0; i < 16; i++) {
        if (ix[i] >= 8) {
            ix[i] -= 16;
        }
        ix[i] *= scale;
    }

    for (s32 j = 0; j < 2; j++) {
        s32 in_vec[16];
        if (j == 0) {
            for (s32 i = 0; i < order; i++) {
                in_vec[i] = state[16 - order + i];
            }
        } else {
            for (s32 i = 0; i < order; i++) {
                in_vec[i] = state[8 - order + i];
            }
        }

        for (s32 i = 0; i < 8; i++) {
            s32 ind = j * 8 + i;
            in_vec[order + i] = ix[ind];
            state[ind] = inner_product(order + i, coefTable[optimalp][i], in_vec) + ix[ind];
        }
    }
}

void my_encodeframe(u8 *out, s16 *inBuffer, s32 *state, const vector<vector<vector<s32>>> &coefTable,
                    s32 order, s32 npredictors) {
    s16 ix[16];
    s32 prediction[16];
    s32 inVector[16];
    s32 saveState[16];
    s32 optimalp = 0;
    s32 scale;
    s32 ie[16];
    s32 e[16];
    f32 min = 1e30;

    for (s32 k = 0; k < npredictors; k++) {
        for (s32 j = 0; j < 2; j++) {
            for (s32 i = 0; i < order; i++) {
                inVector[i] = (j == 0 ? state[16 - order + i] : inBuffer[8 - order + i]);
            }

            for (s32 i = 0; i < 8; i++) {
                prediction[j * 8 + i] = inner_product(order + i, coefTable[k][i], inVector);
                e[j * 8 + i] = inVector[i + order] = inBuffer[j * 8 + i] - prediction[j * 8 + i];
            }
        }

        f32 se = 0.0f;
        for (s32 j = 0; j < 16; j++) {
            se += (f32) e[j] * (f32) e[j];
        }

        if (se < min) {
            min = se;
            optimalp = k;
        }
    }

    for (s32 j = 0; j < 2; j++) {
        for (s32 i = 0; i < order; i++) {
            inVector[i] = (j == 0 ? state[16 - order + i] : inBuffer[8 - order + i]);
        }

        for (s32 i = 0; i < 8; i++) {
            prediction[j * 8 + i] = inner_product(order + i, coefTable[optimalp][i], inVector);
            e[j * 8 + i] = inVector[i + order] = inBuffer[j * 8 + i] - prediction[j * 8 + i];
        }
    }

    for (s32 i = 0; i < 16; i++) {
        ie[i] = clamp_to_s16(e[i]);
    }

    s32 max = 0;
    for (s32 i = 0; i < 16; i++) {
        if (abs(ie[i]) > abs(max)) {
            max = ie[i];
        }
    }

    for (scale = 0; scale <= 12; scale++) {
        if (max <= 7 && max >= -8) {
            break;
        }
        max /= 2;
    }

    for (s32 i = 0; i < 16; i++) {
        saveState[i] = state[i];
    }

    for (s32 nIter = 0, again = 1; nIter < 2 && again; nIter++) {
        again = 0;
        if (nIter == 1) {
            scale++;
        }
        if (scale > 12) {
            scale = 12;
        }

        for (s32 j = 0; j < 2; j++) {
            s32 base = j * 8;
            for (s32 i = 0; i < order; i++) {
                inVector[i] = (j == 0 ? saveState[16 - order + i] : state[8 - order + i]);
            }

            for (s32 i = 0; i < 8; i++) {
                prediction[base + i] = inner_product(order + i, coefTable[optimalp][i], inVector);
                s32 se = inBuffer[base + i] - prediction[base + i];
                ix[base + i] = qsample(se, scale);
                s32 cV = clamp_to_s16(ix[base + i]) - ix[base + i];
                if (cV > 1 || cV < -1) {
                    again = 1;
                }
                ix[base + i] += cV;
                inVector[i + order] = ix[base + i] * (1 << scale);
                state[base + i] = prediction[base + i] + inVector[i + order];
            }
        }
    }

    u8 header = (scale << 4) | (optimalp & 0xf);
    out[0] = header;
    for (s32 i = 0; i < 16; i += 2) {
        u8 c = ((ix[i] & 0xf) << 4) | (ix[i + 1] & 0xf);
        out[1 + i / 2] = c;
    }
}

void permute(s16 *out, s32 *in, s32 scale) {
    for (s32 i = 0; i < 16; i++) {
        out[i] = clamp_to_s16(in[i] - scale / 2 + myrand() % (scale + 1));
    }
}

void write_header(vector<byte> &aiffData, size_t *ofile, const char *id, s32 size) {
    write_bytes_to_vec(id, 4, 1, aiffData, ofile);
    BSWAP32(size);
    write_bytes_to_vec(&size, sizeof(s32), 1, aiffData, ofile);
}

// Much of the original aifc_decode.c remains unedited, but I have integrated its main
// routine to take and return the C++ std::vector<std::byte> array datatype I used in the new code.
// I also vastly improved its memory safety by removing its several unmatched malloc() calls which
// would have leaked memory when incorporated into a larger C++ program.
vector<byte> decode_aifc(const vector<byte> &aifcData) {
    s16 order = -1, nloops = 0, npredictors = -1;
    vector<ALADPCMLoop> aloops;
    vector<vector<vector<s32>>> coefTable;
    s32 state[16], soundPointer = -1, currPos = 0, nSamples = 0;
    Chunk FormChunk;
    ChunkHeader Header;
    CommonChunk CommChunk;
    InstrumentChunk InstChunk;
    SoundDataChunk SndDChunk;

    vector<byte> aiffData;
    size_t inputBufferPosition = 0, outputBufferPosition = 0;

    memset(&InstChunk, 0, sizeof(InstChunk));

    read_bytes_from_vec(&FormChunk, sizeof(FormChunk), 1, aifcData, &inputBufferPosition);
    BSWAP32(FormChunk.ckID);
    BSWAP32(FormChunk.formType);
    if ((FormChunk.ckID != 0x464f524d) || (FormChunk.formType != 0x41494643)) { // FORM, AIFC
        cerr << "not an AIFF-C file" << endl;
        return aiffData;
    }

    for (;;) {
        s32 num = read_bytes_from_vec(&Header, sizeof(Header), 1, aifcData, &inputBufferPosition);
        u32 ts;
        if (num <= 0) {
            break;
        }
        BSWAP32(Header.ckID);
        BSWAP32(Header.ckSize);

        Header.ckSize++;
        Header.ckSize &= ~1;
        s32 cType, offset = inputBufferPosition;

        switch (Header.ckID) {
            case 0x434f4d4d: // COMM
                read_bytes_from_vec(&CommChunk, sizeof(CommChunk), 1, aifcData, &inputBufferPosition);
                BSWAP16(CommChunk.numChannels);
                BSWAP16(CommChunk.numFramesH);
                BSWAP16(CommChunk.numFramesL);
                BSWAP16(CommChunk.sampleSize);
                BSWAP16(CommChunk.compressionTypeH);
                BSWAP16(CommChunk.compressionTypeL);
                cType = (CommChunk.compressionTypeH << 16) + CommChunk.compressionTypeL;
                if (cType != 0x56415043) { // VAPC
                    cerr << "file is of the wrong compression type" << endl;
                    return aiffData;
                }
                if (CommChunk.numChannels != 1) {
                    cerr << "file contains " << CommChunk.numChannels
                         << " channels, only 1 channel supported" << endl;
                    return aiffData;
                }
                if (CommChunk.sampleSize != 16) {
                    cerr << "file contains " << CommChunk.sampleSize
                         << " bit samples, only 16 bit samples supported" << endl;
                    return aiffData;
                }

                nSamples = (CommChunk.numFramesH << 16) + CommChunk.numFramesL;

                // Allow broken input lengths
                if (nSamples % 16) {
                    nSamples--;
                }

                if (nSamples % 16 != 0) {
                    cerr << "number of chunks must be a multiple of 16, found " << nSamples << endl;
                    return aiffData;
                }
                break;

            case 0x53534e44: // SSND
                read_bytes_from_vec(&SndDChunk, sizeof(SndDChunk), 1, aifcData, &inputBufferPosition);
                BSWAP32(SndDChunk.offset);
                BSWAP32(SndDChunk.blockSize);
                assert(SndDChunk.offset == 0);
                assert(SndDChunk.blockSize == 0);
                soundPointer = inputBufferPosition;
                break;

            case 0x4150504c: // APPL
                read_bytes_from_vec(&ts, sizeof(u32), 1, aifcData, &inputBufferPosition);
                BSWAP32(ts);
                if (ts == 0x73746f63) { // stoc
                    u8 len;
                    read_bytes_from_vec(&len, 1, 1, aifcData, &inputBufferPosition);
                    if (len == 11) {
                        char ChunkName[12];
                        s16 version;
                        read_bytes_from_vec(ChunkName, 11, 1, aifcData, &inputBufferPosition);
                        ChunkName[11] = '\0';
                        if (strcmp("VADPCMCODES", ChunkName) == 0) {
                            read_bytes_from_vec(&version, sizeof(s16), 1, aifcData,
                                                &inputBufferPosition);
                            BSWAP16(version);
                            if (version != 1) {
                                cerr << "Unknown codebook chunk version" << endl;
                                return aiffData;
                            }
                            read_aifc_codebook(aifcData, &inputBufferPosition, coefTable, &order,
                                               &npredictors);
                        } else if (strcmp("VADPCMLOOPS", ChunkName) == 0) {
                            read_bytes_from_vec(&version, sizeof(s16), 1, aifcData,
                                                &inputBufferPosition);
                            BSWAP16(version);
                            if (version != 1) {
                                cerr << "Unknown loop chunk version" << endl;
                                return aiffData;
                            }
                            aloops = read_loop_points(aifcData, &inputBufferPosition, &nloops);
                            if (nloops != 1) {
                                cerr << "Only a single loop supported" << endl;
                                return aiffData;
                            }
                        }
                    }
                }
                break;
        }

        inputBufferPosition = offset + Header.ckSize;
    }

    if (!coefTable.size()) {
        cerr << "Codebook missing from bitstream" << endl;
        return aiffData;
    }

    for (s32 i = 0; i < order; i++) {
        state[15 - i] = 0;
    }

    u32 outputBytes = nSamples * sizeof(s16);
    vector<u8> outputBuf(outputBytes);

    inputBufferPosition = soundPointer;
    while (currPos < nSamples) {
        u8 input[9];
        u8 encoded[9];
        s32 lastState[16];
        s32 decoded[16];
        s16 guess[16];
        s16 origGuess[16];

        memcpy(lastState, state, sizeof(lastState));
        read_bytes_from_vec(input, 9, 1, aifcData, &inputBufferPosition);

        // Decode for real
        my_decodeframe(input, state, order, coefTable);
        memcpy(decoded, state, sizeof(lastState));

        // Create a guess from that, by clamping to 16 bits
        for (s32 i = 0; i < 16; i++) {
            origGuess[i] = clamp_to_s16(state[i]);
        }

        // Encode the guess
        memcpy(state, lastState, sizeof(lastState));
        memcpy(guess, origGuess, sizeof(guess));
        my_encodeframe(encoded, guess, state, coefTable, order, npredictors);

        // If it doesn't match, randomly round numbers until it does.
        if (memcmp(input, encoded, 9) != 0) {
            s32 scale = 1 << (input[0] >> 4);
            do {
                permute(guess, decoded, scale);
                memcpy(state, lastState, sizeof(lastState));
                my_encodeframe(encoded, guess, state, coefTable, order, npredictors);
            } while (memcmp(input, encoded, 9) != 0);

            // Bring the matching closer to the original decode (not strictly
            // necessary, but it will move us closer to the target on average).
            for (s32 failures = 0; failures < 50; failures++) {
                s32 ind = myrand() % 16;
                s32 old = guess[ind];
                if (old == origGuess[ind]) {
                    continue;
                }
                guess[ind] = origGuess[ind];
                if (myrand() % 2) {
                    guess[ind] += (old - origGuess[ind]) / 2;
                }
                memcpy(state, lastState, sizeof(lastState));
                my_encodeframe(encoded, guess, state, coefTable, order, npredictors);
                if (memcmp(input, encoded, 9) == 0) {
                    failures = -1;
                } else {
                    guess[ind] = old;
                }
            }
        }

        memcpy(state, decoded, sizeof(lastState));
        BSWAP16_MANY(guess, 16);
        memcpy(outputBuf.data() + currPos * 2, guess, sizeof(guess));
        currPos += 16;
    }

    // Write an incomplete file header. We'll fill in the size later.
    write_bytes_to_vec("FORM\0\0\0\0AIFF", 12, 1, aiffData, &outputBufferPosition);

    // Subtract 4 from the COMM size to skip the compression field.
    write_header(aiffData, &outputBufferPosition, "COMM", sizeof(CommonChunk) - 4);
    CommChunk.numFramesH = nSamples >> 16;
    CommChunk.numFramesL = nSamples & 0xffff;
    BSWAP16(CommChunk.numChannels);
    BSWAP16(CommChunk.numFramesH);
    BSWAP16(CommChunk.numFramesL);
    BSWAP16(CommChunk.sampleSize);
    write_bytes_to_vec(&CommChunk, sizeof(CommonChunk) - 4, 1, aiffData, &outputBufferPosition);

    if (nloops > 0) {
        s32 startPos = aloops[0].start, endPos = aloops[0].end;
        const char *markerNames[2] = { "start", "end" };
        Marker markers[2] = {
            { 1, static_cast<u16>(startPos >> 16), static_cast<u16>(startPos & 0xffff) },
            { 2, static_cast<u16>(endPos >> 16), static_cast<u16>(endPos & 0xffff) }
        };
        write_header(aiffData, &outputBufferPosition, "MARK", 2 + 2 * sizeof(Marker) + 1 + 5 + 1 + 3);
        s16 numMarkers = bswap16(2);
        write_bytes_to_vec(&numMarkers, sizeof(s16), 1, aiffData, &outputBufferPosition);
        for (s32 i = 0; i < 2; i++) {
            u8 len = static_cast<u8>(strlen(markerNames[i]) & 0xFF);
            BSWAP16(markers[i].MarkerID);
            BSWAP16(markers[i].positionH);
            BSWAP16(markers[i].positionL);
            write_bytes_to_vec(&markers[i], sizeof(Marker), 1, aiffData, &outputBufferPosition);
            write_bytes_to_vec(&len, 1, 1, aiffData, &outputBufferPosition);
            write_bytes_to_vec(markerNames[i], len, 1, aiffData, &outputBufferPosition);
        }

        write_header(aiffData, &outputBufferPosition, "INST", sizeof(InstrumentChunk));
        InstChunk.sustainLoop.playMode = bswap16(1);
        InstChunk.sustainLoop.beginLoop = bswap16(1);
        InstChunk.sustainLoop.endLoop = bswap16(2);
        InstChunk.releaseLoop.playMode = 0;
        InstChunk.releaseLoop.beginLoop = 0;
        InstChunk.releaseLoop.endLoop = 0;
        write_bytes_to_vec(&InstChunk, sizeof(InstrumentChunk), 1, aiffData, &outputBufferPosition);
    }

    // Save the coefficient table for use when encoding. Ideally this wouldn't
    // be needed and "tabledesign -s 1" would generate the right table, but in
    // practice it's difficult to adjust samples to make that happen.
    write_header(aiffData, &outputBufferPosition, "APPL",
                 4 + 12 + sizeof(CodeChunk) + npredictors * order * 8 * 2);
    write_bytes_to_vec("stoc", 4, 1, aiffData, &outputBufferPosition);
    CodeChunk cChunk;
    cChunk.version = bswap16(1);
    cChunk.order = bswap16(order);
    cChunk.nEntries = bswap16(npredictors);
    write_bytes_to_vec("\x0bVADPCMCODES", 12, 1, aiffData, &outputBufferPosition);
    write_bytes_to_vec(&cChunk, sizeof(CodeChunk), 1, aiffData, &outputBufferPosition);
    for (s32 i = 0; i < npredictors; i++) {
        for (s32 j = 0; j < order; j++) {
            for (s32 k = 0; k < 8; k++) {
                s16 ts = bswap16(coefTable[i][k][j]);
                write_bytes_to_vec(&ts, sizeof(s16), 1, aiffData, &outputBufferPosition);
            }
        }
    }

    write_header(aiffData, &outputBufferPosition, "SSND", outputBytes + 8);
    SndDChunk.offset = 0;
    SndDChunk.blockSize = 0;
    write_bytes_to_vec(&SndDChunk, sizeof(SoundDataChunk), 1, aiffData, &outputBufferPosition);
    write_bytes_to_vec(outputBuf.data(), outputBytes, 1, aiffData, &outputBufferPosition);

    // Fix the size in the header
    s32 fileSize = bswap32(outputBufferPosition - 8);
    outputBufferPosition = 4;
    write_bytes_to_vec(&fileSize, 4, 1, aiffData, &outputBufferPosition);

    return aiffData;
}
// End translated aifc_decode.c

// End utilities

// Classes
class Sound {
  public:
    uint32_t sample_addr = 0;
    double tuning;

    Sound(const uint32_t sample_addr, const double tuning) : sample_addr(sample_addr), tuning(tuning) {
    }

    Sound(const Sound &s) {
        sample_addr = s.sample_addr;
        tuning = s.tuning;
    }

    Sound() = default;

    Sound &operator=(const Sound &sound) = default;

    Sound(const vector<byte> &data) {
        sample_addr = READ_32_BITS(data, 0);
        tuning = static_cast<double>(bit_cast<float>(READ_32_BITS(data, 4)));
        if (sample_addr == 0) {
            assert(tuning == 0.0f);
        }
    }
};

class Drum {
  public:
    Sound sound;

    Drum(const Sound &sound) : sound(sound) {
    }

    Drum(const Drum &d) {
        sound = d.sound;
    }

    Drum() = default;

    Drum &operator=(const Drum &drum) = default;

    Drum(const vector<byte> &data) {
        byte loaded = data[2], pad = data[3];
        uint32_t envelope_addr = READ_32_BITS(data, 12);
        assert(static_cast<uint8_t>(loaded) == 0);
        assert(static_cast<uint8_t>(pad) == 0);
        assert(envelope_addr != 0);
        sound = Sound({ data.begin() + 4, data.begin() + 12 });
    }
};

class Instrument {
  public:
    Sound sound_lo, sound_med, sound_hi;

    Instrument(const Sound &sound_lo, const Sound &sound_med, const Sound &sound_hi)
        : sound_lo(sound_lo), sound_med(sound_med), sound_hi(sound_hi) {
    }

    Instrument(const Instrument &i) {
        sound_lo = i.sound_lo;
        sound_med = i.sound_med;
        sound_hi = i.sound_hi;
    }

    Instrument() = default;

    Instrument &operator=(const Instrument &instrmnt) = default;

    Instrument(const vector<byte> &data) {
        byte normal_range_lo = data[1], normal_range_hi = data[2];
        uint32_t envelope_addr = READ_32_BITS(data, 4);
        assert(envelope_addr != 0);
        sound_lo = Sound({ data.begin() + 8, data.begin() + 16 });
        sound_med = Sound({ data.begin() + 16, data.begin() + 24 });
        sound_hi = Sound({ data.begin() + 24, data.end() });
        if (sound_lo.sample_addr == 0) {
            assert(static_cast<uint8_t>(normal_range_lo) == 0);
        }
        if (sound_hi.sample_addr == 0) {
            assert(static_cast<uint8_t>(normal_range_hi) == 127);
        }
    }
};

class Book {
  public:
    int16_t order, npredictors;
    vector<int16_t> table;

    Book(const uint32_t order, const uint32_t npredictors, const vector<int16_t> &table)
        : order(order), npredictors(npredictors), table(table) {
    }

    Book(const Book &b) {
        order = b.order;
        npredictors = b.npredictors;
        table = b.table;
    }

    Book() = default;

    Book &operator=(const Book &book) = default;

    Book(const uint32_t addr, const vector<byte> &bank_data) {
        order = READ_32_BITS(bank_data, addr);
        npredictors = READ_32_BITS(bank_data, addr + 4);
        assert(order == 2);
        assert(npredictors == 2);
        for (int32_t i = 0; i < 16 * order * npredictors; i += 2) {
            table.push_back(READ_16_BITS(bank_data, addr + 8 + i));
        }
    }
};

ALADPCMLoop::ALADPCMLoop(const uint32_t start, const uint32_t end, const uint32_t count,
                         const vector<int16_t> &state)
    : start(start), end(end), count(count), state(state) {
}

ALADPCMLoop::ALADPCMLoop(const ALADPCMLoop &l) {
    start = l.start;
    end = l.end;
    count = l.count;
    state = l.state;
}

ALADPCMLoop::ALADPCMLoop(const uint32_t addr, const vector<byte> &bank_data) {
    start = READ_32_BITS(bank_data, addr);
    end = READ_32_BITS(bank_data, addr + 4);
    count = READ_32_BITS(bank_data, addr + 8);
    uint32_t pad = READ_32_BITS(bank_data, addr + 12);
    assert(pad == 0);
    if (!count) {
        return;
    }
    for (size_t i = 0; i < 32; i += 2) {
        state.push_back(READ_16_BITS(bank_data, addr + 16 + i));
    }
}

class AifcEntry {
  public:
    string filename;
    vector<byte> data;
    Book book;
    ALADPCMLoop loop;
    vector<double> tunings;

    AifcEntry(const string &filename, const vector<byte> &data, const Book &book,
              const ALADPCMLoop &loop, const vector<double> &tunings)
        : filename(filename), data(data), book(book), loop(loop), tunings(tunings) {
    }

    AifcEntry(const AifcEntry &ae) {
        filename = ae.filename;
        data = ae.data;
        book = ae.book;
        loop = ae.loop;
        tunings = ae.tunings;
    }

    AifcEntry() = default;
};

class BankHeader {
  public:
    uint32_t num_instrmts, num_drums;
    BankHeader(const uint32_t num_instrmts, const uint32_t num_drums)
        : num_instrmts(num_instrmts), num_drums(num_drums) {
    }

    BankHeader(const BankHeader &bh) {
        num_instrmts = bh.num_instrmts;
        num_drums = bh.num_drums;
    }

    BankHeader() = default;

    BankHeader(const vector<byte> &header) {
        num_instrmts = READ_32_BITS(header, 0);
        num_drums = READ_32_BITS(header, 4);
        uint32_t shared = READ_32_BITS(header, 8);

        assert(shared == 0 || shared == 1);
    }
};

// SampleBank
class SampleBank {
  public:
    uint32_t bank_index;
    vector<uint32_t> ctl_indices;
    vector<AifcEntry> entries;

    SampleBank(const uint32_t bank_index, const vector<byte> &data)
        : bank_index(bank_index), data(data) {
    }

    SampleBank(const SampleBank &sb) {
        bank_index = sb.bank_index;
        ctl_indices = sb.ctl_indices;
        data = sb.data;
    }

    SampleBank() = default;

    void parse_sample(const vector<byte> &sample_data, const vector<byte> &bank_data,
                      const vector<double> &tunings, const string &filename);

    void parse_ctl(const BankHeader &parsed_header, const vector<byte> &data,
                   map<const uint32_t, const string> &address_to_filename, const uint32_t offset);

  private:
    vector<byte> data;
};

void SampleBank::parse_sample(const vector<byte> &sample_data, const vector<byte> &bank_data,
                              const vector<double> &tunings, const string &filename) {

    if (filename == "") {
        // duplicate sample, not necessary
        return;
    }

    uint32_t zero = READ_32_BITS(sample_data, 0), addr = READ_32_BITS(sample_data, 4),
             raw_loop = READ_32_BITS(sample_data, 8), raw_book = READ_32_BITS(sample_data, 12),
             sample_size = READ_32_BITS(sample_data, 16);

    assert(zero == 0);
    assert(raw_loop != 0);
    assert(raw_book != 0);
    assert(sample_size % 2 == 0);
    if (sample_size % 9 != 0) {
        assert(sample_size % 9 == 1);
        sample_size -= 1;
    }

    Book book(raw_book, bank_data);
    ALADPCMLoop loop(raw_loop, bank_data);

    AifcEntry *already_parsed_entry = nullptr;
    for (auto &entry : entries) {
        if (filename == entry.filename) {
            already_parsed_entry = &entry;
            break;
        }
    }

    if (already_parsed_entry != nullptr) {
        assert(already_parsed_entry->book.order == book.order);
        assert(already_parsed_entry->book.npredictors == book.npredictors);
        assert(already_parsed_entry->book.table == book.table);
        assert(already_parsed_entry->loop.start == loop.start);
        assert(already_parsed_entry->loop.end == loop.end);
        assert(already_parsed_entry->loop.count == loop.count);
        assert(already_parsed_entry->loop.state == loop.state);
        assert(already_parsed_entry->data.size() == sample_size);
        return;
    }

    const auto aifc_data = vector<byte>(data.begin() + addr, data.begin() + addr + sample_size);
    auto entry = AifcEntry(filename, aifc_data, book, loop, tunings);
    entries.push_back(entry);
}

void SampleBank::parse_ctl(const BankHeader &parsed_header, const vector<byte> &bank_data,
                           map<const uint32_t, const string> &address_to_filename,
                           const uint32_t offset) {
    uint32_t drum_base_addr = READ_32_BITS(bank_data, 0);
    vector<uint32_t> drum_addrs;

    if (parsed_header.num_drums != 0) {
        assert(drum_base_addr != 0);
        for (size_t i = 0; i < parsed_header.num_drums; i++) {
            uint32_t drum_addr = READ_32_BITS(bank_data, drum_base_addr + i * 4);
            assert(drum_addr != 0);
            drum_addrs.push_back(drum_addr);
        }
    } else {
        assert(drum_base_addr == 0);
    }

    uint32_t instrmt_base_addr = 4;
    vector<uint32_t> instrmt_addrs, instrmt_list(parsed_header.num_instrmts, 0);

    for (size_t i = 0; i < parsed_header.num_instrmts; i++) {
        uint32_t instrmt_addr = READ_32_BITS(bank_data, instrmt_base_addr + i * 4);
        if (instrmt_addr == 0) {
            instrmt_list[i] = 0;
        } else {
            instrmt_list[i] = instrmt_addr;
            instrmt_addrs.push_back(instrmt_addr);
        }
    }

    if (!drum_addrs.empty() && !instrmt_addrs.empty()) {
        assert(*max_element(instrmt_addrs.begin(), instrmt_addrs.end())
               < *min_element(drum_addrs.begin(), drum_addrs.end()));
    }

    assert(set<uint32_t>(instrmt_addrs.begin(), instrmt_addrs.end()).size() == instrmt_addrs.size());
    assert(set<uint32_t>(drum_addrs.begin(), drum_addrs.end()).size() == drum_addrs.size());

    vector<Instrument> instrmts;
    for (uint32_t instrmt_addr : instrmt_addrs) {
        auto instrmt = Instrument(
            vector<byte>(bank_data.begin() + instrmt_addr, bank_data.begin() + instrmt_addr + 32));
        instrmts.push_back(instrmt);
    }

    vector<Drum> drums;
    for (uint32_t drum_addr : drum_addrs) {
        auto drum =
            Drum(vector<byte>(bank_data.begin() + drum_addr, bank_data.begin() + drum_addr + 16));
        drums.push_back(drum);
    }

    set<uint32_t> sample_addrs;
    map<uint32_t, vector<double>> tunings;

    for (const auto &instrmt : instrmts) {
        for (const auto &sound : { instrmt.sound_lo, instrmt.sound_med, instrmt.sound_hi }) {
            if (sound.sample_addr != 0) {
                sample_addrs.insert(sound.sample_addr);
                tunings[sound.sample_addr].push_back(sound.tuning);
            }
        }
    }

    for (const auto &drum : drums) {
        sample_addrs.insert(drum.sound.sample_addr);
        tunings[drum.sound.sample_addr].push_back(drum.sound.tuning);
    }

    for (const auto addr : sample_addrs) {
        uint32_t sample_size = 20;
        const auto sample_data =
            vector<byte>(bank_data.begin() + addr, bank_data.begin() + addr + sample_size);
        parse_sample(sample_data, bank_data, tunings[addr], address_to_filename[offset + addr]);
    }
}
// End SampleBank

// AiffWriter
class AiffWriter {
  public:
    AiffWriter(ofstream &out) : out(out) {
    }

    void add_section(const string &tp, const vector<byte> &data);
    void add_custom_section(const string &tp, const vector<byte> &data);
    void write(const AifcEntry &entry);
    void finish(void);

  private:
    ofstream &out;
    vector<pair<string, vector<byte>>> sections;
};

void AiffWriter::add_section(const string &tp, const vector<byte> &data) {
    sections.emplace_back(tp, data);
}

void AiffWriter::add_custom_section(const string &tp, const vector<byte> &data) {
    string stoc_string = "stoc";
    vector<byte> custom_data(stoc_string.size()), tp_data = pstring(tp);
    transform(stoc_string.begin(), stoc_string.end(), custom_data.begin(), INTO_BYTES);
    custom_data.insert(custom_data.end(), tp_data.begin(), tp_data.end());
    custom_data.insert(custom_data.end(), data.begin(), data.end());
    add_section("APPL", custom_data);
}

void AiffWriter::finish(void) {
    string form_string = "FORM", aifc_string = "AIFC";

    // total_size_pad is a place where some .aiff files have size information but it's
    // not necessary for this game
    vector<byte> form_chars(form_string.size()), aifc_chars(aifc_string.size()),
        total_size_pad(4, static_cast<byte>(0)), out_vec;
    transform(form_string.begin(), form_string.end(), form_chars.begin(), INTO_BYTES);
    transform(aifc_string.begin(), aifc_string.end(), aifc_chars.begin(), INTO_BYTES);
    out_vec.insert(out_vec.end(), form_chars.begin(), form_chars.end());
    out_vec.insert(out_vec.end(), total_size_pad.begin(), total_size_pad.end());
    out_vec.insert(out_vec.end(), aifc_chars.begin(), aifc_chars.end());

    for (const auto &[tp, data] : sections) {
        vector<byte> tp_chars(tp.size());
        transform(tp.begin(), tp.end(), tp_chars.begin(), INTO_BYTES);
        out_vec.insert(out_vec.end(), tp_chars.begin(), tp_chars.end());
        uint32_t size = data.size();
        vector<byte> size_bytes(4);
        WRITE_32_BITS(size, size_bytes, 0);
        out_vec.insert(out_vec.end(), size_bytes.begin(), size_bytes.end());
        out_vec.insert(out_vec.end(), data.begin(), data.end());
        if (size % 2) {
            out_vec.insert(out_vec.end(), static_cast<byte>('\0'));
        }
    }

    auto aiff = decode_aifc(out_vec);

    out.write(reinterpret_cast<const char *>(aiff.data()), aiff.size());
    out.close();
}

void AiffWriter::write(const AifcEntry &entry) {
    int16_t num_channels = 1, sample_size = 16;
    auto data = entry.data;
    assert(data.size() % 9 == 0);
    if (data.size() % 2) {
        data.push_back(static_cast<byte>('\0'));
    }
    // (Computing num_frames this way makes it off by one when the data length
    // is odd. It matches vadpcm_enc, though.)
    uint32_t num_frames = data.size() * 16 / 9;

    double sample_rate;
    if (entry.tunings.size() == 1) {
        sample_rate = 32000 * entry.tunings[0];
    } else {
        double min_tuning = *min_element(entry.tunings.begin(), entry.tunings.end());
        double max_tuning = *max_element(entry.tunings.begin(), entry.tunings.end());
        if (min_tuning <= 0.5 && max_tuning >= 0.5) {
            sample_rate = 16000;
        } else if (min_tuning <= 1.0 && max_tuning >= 1.0) {
            sample_rate = 32000;
        } else if (min_tuning <= 1.5 && max_tuning >= 1.5) {
            sample_rate = 48000;
        } else if (min_tuning <= 2.5 && max_tuning >= 2.5) {
            sample_rate = 80000;
        } else {
            sample_rate = 16000 * (min_tuning + max_tuning);
        }
    }

    vector<byte> comm_section(18);
    auto sample_rate_bytes = serialize_f80(sample_rate);
    WRITE_16_BITS(num_channels, comm_section, 0);
    WRITE_32_BITS(num_frames, comm_section, 2);
    WRITE_16_BITS(sample_size, comm_section, 6);
    for (size_t i = 0; i < 10; i++) {
        comm_section[i + 8] = sample_rate_bytes[i];
    }

    string vapc_string = "VAPC", vadpcm_string = "VADPCM ~4-1";
    vector<byte> vapc_data(vapc_string.size()), vadpcm_data = pstring(vadpcm_string);
    transform(vapc_string.begin(), vapc_string.end(), vapc_data.begin(), INTO_BYTES);
    comm_section.insert(comm_section.end(), vapc_data.begin(), vapc_data.end());
    comm_section.insert(comm_section.end(), vadpcm_data.begin(), vadpcm_data.end());
    add_section("COMM", comm_section);

    vector<byte> instrmt_section(20, static_cast<byte>('\0'));
    add_section("INST", instrmt_section);

    vector<byte> vadpcm_codes(6);
    WRITE_16_BITS(1, vadpcm_codes, 0);
    WRITE_16_BITS(entry.book.order, vadpcm_codes, 2);
    WRITE_16_BITS(entry.book.npredictors, vadpcm_codes, 4);
    for (int16_t value : entry.book.table) {
        vadpcm_codes.push_back(static_cast<byte>((value >> 8) & 0xFF));
        vadpcm_codes.push_back(static_cast<byte>(value & 0xFF));
    }
    add_custom_section("VADPCMCODES", vadpcm_codes);

    vector<byte> ssnd_section(8, static_cast<byte>(0));
    ssnd_section.insert(ssnd_section.end(), data.begin(), data.end());
    add_section("SSND", ssnd_section);

    if (entry.loop.count != 0) {
        vector<byte> vadpcm_loops(16);
        WRITE_16_BITS(1, vadpcm_loops, 0);
        WRITE_16_BITS(1, vadpcm_loops, 2);
        WRITE_32_BITS(entry.loop.start, vadpcm_loops, 4);
        WRITE_32_BITS(entry.loop.end, vadpcm_loops, 8);
        WRITE_32_BITS(entry.loop.count, vadpcm_loops, 12);
        for (int16_t value : entry.loop.state) {
            vadpcm_loops.push_back(static_cast<byte>((value >> 8) & 0xFF));
            vadpcm_loops.push_back(static_cast<byte>(value & 0xFF));
        }
        add_custom_section("VADPCMLOOPS", vadpcm_loops);
    }

    finish();
}
// End AiffWriter

// estimate.c translated to C++

// https://en.wikipedia.org/wiki/Durbin%E2%80%93Watson_statistic ?
// "detects the presence of autocorrelation at lag 1 in the residuals (prediction errors)"
int durbin(const vector<double> &arg0, const int n, vector<double> &arg2, vector<double> &arg3) {
    int i, j;
    double sum, div;
    int ret;

    arg3[0] = 1.0;
    div = arg0[0];
    ret = 0;

    for (i = 1; i <= n; i++) {
        sum = 0.0;
        for (j = 1; j <= i - 1; j++) {
            sum += arg3[j] * arg0[i - j];
        }

        arg3[i] = (div > 0.0 ? -(arg0[i] + sum) / div : 0.0);
        arg2[i] = arg3[i];

        if (fabs(arg2[i]) > 1.0) {
            ret++;
        }

        for (j = 1; j < i; j++) {
            arg3[j] += arg3[i - j] * arg3[i];
        }

        div *= 1.0 - arg3[i] * arg3[i];
    }

    return ret;
}

void afromk(const vector<double> &in, vector<double> &out, const size_t n) {
    out[0] = 1.0f;
    for (size_t i = 1; i <= n; i++) {
        out[i] = in[i];
        for (size_t j = 1; j <= i - 1; j++) {
            out[j] += out[i - j] * out[i];
        }
    }
}

int kfroma(vector<double> &in, vector<double> &out, const size_t n) {
    double div;
    double temp;
    vector<double> next;
    int ret;

    ret = 0;
    next.resize(n + 1);

    out[n] = in[n];
    for (size_t i = n - 1; i >= 1; i--) {
        for (size_t j = 0; j <= i; j++) {
            temp = out[i + 1];
            div = 1.0 - (temp * temp);
            if (div == 0.0) {
                return 1;
            }
            next[j] = (in[j] - in[i + 1 - j] * temp) / div;
        }

        for (size_t j = 0; j <= i; j++) {
            in[j] = next[j];
        }

        out[i] = next[i];
        if (fabs(out[i]) > 1.0) {
            ret++;
        }
    }

    return ret;
}

void rfroma(const vector<double> &arg0, const size_t n, vector<double> &arg2) {
    vector<vector<double>> mat;
    double div;

    mat.resize(n + 1);
    mat[n].resize(n + 1);
    mat[n][0] = 1.0;
    for (size_t i = 1; i <= n; i++) {
        mat[n][i] = -arg0[i];
    }

    for (size_t i = n; i >= 1; i--) {
        mat[i - 1].resize(i);
        div = 1.0 - mat[i][i] * mat[i][i];
        for (size_t j = 1; j <= i - 1; j++) {
            mat[i - 1][j] = (mat[i][i - j] * mat[i][i] + mat[i][j]) / div;
        }
    }

    arg2[0] = 1.0;
    for (size_t i = 1; i <= n; i++) {
        arg2[i] = 0.0;
        for (size_t j = 1; j <= i; j++) {
            arg2[i] += mat[i][j] * arg2[i - j];
        }
    }
}

double model_dist(const vector<double> &arg0, const vector<double> &arg1, const size_t n) {
    vector<double> sp3C, sp38;
    double ret;

    sp3C.resize(n + 1);
    sp38.resize(n + 1);
    rfroma(arg1, n, sp3C);

    for (size_t i = 0; i <= n; i++) {
        sp38[i] = 0.0;
        for (size_t j = 0; j <= n - i; j++) {
            sp38[i] += arg0[j] * arg0[i + j];
        }
    }

    ret = sp38[0] * sp3C[0];
    for (size_t i = 1; i <= n; i++) {
        ret += 2 * sp3C[i] * sp38[i];
    }

    return ret;
}

// compute autocorrelation matrix?
void acmat(const vector<short> &in, const size_t n, const size_t m, vector<vector<double>> &out) {
    for (size_t i = 1; i <= n; i++) {
        for (size_t j = 1; j <= n; j++) {
            out[i][j] = 0.0f;
            for (size_t k = 0; k < m; k++) {
                out[i][j] += in[k - i] * in[k - j];
            }
        }
    }
}

// compute autocorrelation vector?
void acvect(const vector<short> &in, const size_t n, const size_t m, vector<double> &out) {
    for (size_t i = 0; i <= n; i++) {
        out[i] = 0.0f;
        for (size_t j = 0; j < m; j++) {
            out[i] -= in[j - i] * in[j];
        }
    }
}

/**
 * Replaces a real n-by-n matrix "a" with the LU decomposition of a row-wise
 * permutation of itself.
 *
 * Input parameters:
 * a: The matrix which is operated on. 1-indexed; it should be of size
 *    (n+1) x (n+1), and row/column index 0 is not used.
 * n: The size of the matrix.
 *
 * Output parameters:
 * indx: The row permutation performed. 1-indexed; it should be of size n+1,
 *       and index 0 is not used.
 * d: the determinant of the permutation matrix.
 *
 * Returns 1 to indicate failure if the matrix is singular or has zeroes on the
 * diagonal, 0 on success.
 *
 * Derived from ludcmp in "Numerical Recipes in C: The Art of Scientific Computing",
 * with modified error handling.
 */
int lud(vector<vector<double>> &a, const size_t n, vector<int> &indx, int *d) {
    size_t imax;
    double big, dum, sum, temp, min, max;
    vector<double> vv;

    vv.resize(n + 1);
    *d = 1;
    for (size_t i = 1; i <= n; i++) {
        big = 0.0;
        for (size_t j = 1; j <= n; j++) {
            if ((temp = fabs(a[i][j])) > big) {
                big = temp;
            }
        }
        if (big == 0.0) {
            return 1;
        }
        vv[i] = 1.0 / big;
    }
    for (size_t j = 1; j <= n; j++) {
        for (size_t i = 1; i < j; i++) {
            sum = a[i][j];
            for (size_t k = 1; k < i; k++) {
                sum -= a[i][k] * a[k][j];
            }
            a[i][j] = sum;
        }
        big = 0.0;
        for (size_t i = j; i <= n; i++) {
            sum = a[i][j];
            for (size_t k = 1; k < j; k++) {
                sum -= a[i][k] * a[k][j];
            }
            a[i][j] = sum;
            if ((dum = vv[i] * fabs(sum)) >= big) {
                big = dum;
                imax = i;
            }
        }
        if (j != imax) {
            for (size_t k = 1; k <= n; k++) {
                dum = a[imax][k];
                a[imax][k] = a[j][k];
                a[j][k] = dum;
            }
            *d = -(*d);
            vv[imax] = vv[j];
        }
        indx[j] = imax;
        if (a[j][j] == 0.0) {
            return 1;
        }
        if (j != n) {
            dum = 1.0 / (a[j][j]);
            for (size_t i = j + 1; i <= n; i++) {
                a[i][j] *= dum;
            }
        }
    }

    min = 1e10;
    max = 0.0;
    for (size_t i = 1; i <= n; i++) {
        temp = fabs(a[i][i]);
        if (temp < min) {
            min = temp;
        }
        if (temp > max) {
            max = temp;
        }
    }
    return min / max < 1e-10 ? 1 : 0;
}

/**
 * Solves the set of n linear equations Ax = b, using LU decomposition
 * back-substitution.
 *
 * Input parameters:
 * a: The LU decomposition of a matrix, created by "lud".
 * n: The size of the matrix.
 * indx: Row permutation vector, created by "lud".
 * b: The vector b in the equation. 1-indexed; is should be of size n+1, and
 *    index 0 is not used.
 *
 * Output parameters:
 * b: The output vector x. 1-indexed.
 *
 * From "Numerical Recipes in C: The Art of Scientific Computing".
 */
void lubksb(vector<vector<double>> &a, const int n, vector<int> &indx, vector<double> &b) {
    int i, ii = 0, ip, j;
    double sum;

    for (i = 1; i <= n; i++) {
        ip = indx[i];
        sum = b[ip];
        b[ip] = b[i];
        if (ii)
            for (j = ii; j <= i - 1; j++)
                sum -= a[i][j] * b[j];
        else if (sum)
            ii = i;
        b[i] = sum;
    }

    for (i = n; i >= 1; i--) {
        sum = b[i];
        for (j = i + 1; j <= n; j++)
            sum -= a[i][j] * b[j];
        b[i] = sum / a[i][i];
    }
}
// End translated estimate.c

// codebook.c translated to C++
void split(vector<vector<double>> &table, const vector<double> &delta, const size_t order,
           const size_t npredictors, const double scale) {
    for (size_t i = 0; i < npredictors; i++) {
        for (size_t j = 0; j <= order; j++) {
            table[i + npredictors][j] = table[i][j] + delta[j] * scale;
        }
    }
}

void refine(vector<vector<double>> &table, const size_t order, const size_t npredictors,
            const vector<vector<double>> &data, const size_t dataSize, const size_t refineIters) {
    vector<vector<double>> rsums;
    vector<int> counts; // spD0
    vector<double> temp_s7;
    double dist, bestValue;
    size_t bestIndex;

    rsums.resize(npredictors);
    for (auto &rsums_element : rsums) {
        rsums_element.resize(order + 1);
    }

    counts.resize(npredictors);
    temp_s7.resize(order + 1);

    for (size_t iter = 0; iter < refineIters; iter++) {
        for (size_t i = 0; i < npredictors; i++) {
            counts[i] = 0;
            for (size_t j = 0; j <= order; j++) {
                rsums[i][j] = 0.0;
            }
        }

        for (size_t i = 0; i < dataSize; i++) {
            bestValue = 1e30;
            bestIndex = 0;

            for (size_t j = 0; j < npredictors; j++) {
                dist = model_dist(table[j], data[i], order);
                if (dist < bestValue) {
                    bestValue = dist;
                    bestIndex = j;
                }
            }

            counts[bestIndex]++;
            rfroma(data[i], order, temp_s7);
            for (size_t j = 0; j <= order; j++) {
                rsums[bestIndex][j] += temp_s7[j];
            }
        }

        for (size_t i = 0; i < npredictors; i++) {
            if (counts[i] > 0) {
                for (size_t j = 0; j <= order; j++) {
                    rsums[i][j] /= counts[i];
                }
            }
        }

        for (size_t i = 0; i < npredictors; i++) {
            durbin(rsums[i], order, temp_s7, table[i]);

            for (size_t j = 1; j <= order; j++) {
                if (temp_s7[j] >= 1.0) {
                    temp_s7[j] = 0.9999999999;
                }
                if (temp_s7[j] <= -1.0) {
                    temp_s7[j] = -0.9999999999;
                }
            }

            afromk(temp_s7, table[i], order);
        }
    }
}
// End translated codebook.c

// print.c translated to C++
int write_tabledesign_codebook_entry(ofstream &out, vector<double> &row, const size_t order) {
    vector<vector<double>> table;
    double fval;
    int ival, overflows;

    table.resize(8);

    for (auto &table_element : table) {
        table_element.resize(order);
    }

    for (size_t i = 0; i < order; i++) {
        for (size_t j = 0; j < i; j++) {
            table[i][j] = 0.0;
        }

        for (size_t j = i; j < order; j++) {
            table[i][j] = -row[order - j + i];
        }
    }

    for (size_t i = order; i < 8; i++) {
        for (size_t j = 0; j < order; j++) {
            table[i][j] = 0.0;
        }
    }

    for (size_t i = 1; i < 8; i++) {
        for (size_t j = 1; j <= order; j++) {
            if (static_cast<int>(i) - static_cast<int>(j) >= 0) {
                for (size_t k = 0; k < order; k++) {
                    table[i][k] -= row[j] * table[i - j][k];
                }
            }
        }
    }

    overflows = 0;
    for (size_t i = 0; i < order; i++) {
        for (size_t j = 0; j < 8; j++) {
            fval = table[j][i] * 2048.0;
            if (fval < 0.0) {
                ival = (int) (fval - 0.5);
                if (ival < -0x8000) {
                    overflows++;
                }
            } else {
                ival = (int) (fval + 0.5);
                if (ival >= 0x8000) {
                    overflows++;
                }
            }
            out << setw(5) << ival << " ";
        }
        out << endl;
    }

    return overflows;
}
// End translated print.c

// tabledesign.c translated to C++ (except for calls to external C library audiofile)
int write_tabledesign_codebook(const string &filename, ofstream &out) {
    double thresh;
    vector<short> temp_s3;
    vector<int> perm;
    vector<double> spF4, vec, splitDelta;
    vector<vector<double>> mat, temp_s1, data;
    size_t order, bits, refineIters, frameSize, npredictors, numOverflows, dataSize;
    int permDet, sampleFormat, sampleWidth, channels, tracks;

    AFframecount frameCount;
    AFfilehandle afFile;

    order = 2;
    bits = 1;
    refineIters = 2;
    frameSize = 16;
    numOverflows = 0;
    thresh = 10.0;

    afFile = afOpenFile(filename.c_str(), "rb", nullptr);
    if (afFile == nullptr) {
        cerr << "write_tabledesign_codebook(): input AIFC file " << filename << " could not be opened."
             << endl;
        return 1;
    }

    channels = afGetChannels(afFile, AF_DEFAULT_TRACK);
    if (channels != 1) {
        cerr << "write_tabledesign_codebook(): file " << filename << " contains " << channels
             << " channels, only 1 channel supported." << endl;
        return 2;
    }

    tracks = afGetTrackIDs(afFile, nullptr);
    if (tracks != 1) {
        cerr << "write_tabledesign_codebook(): file " << filename << " contains " << tracks
             << " tracks, only 1 track supported." << endl;
        return 3;
    }

    afGetSampleFormat(afFile, AF_DEFAULT_TRACK, &sampleFormat, &sampleWidth);
    if (sampleWidth != 16) {
        cerr << "write_tabledesign_codebook(): file " << filename << " contains " << sampleWidth
             << " bit samples, only 16 bit samples supported." << endl;
        return 4;
    }

    temp_s1.resize(1 << bits);
    for (auto &temp_s1_element : temp_s1) {
        temp_s1_element.resize(order + 1);
    }

    splitDelta.resize(order + 1);
    temp_s3.resize(frameSize * 2);
    for (auto &temp_s3_element : temp_s3) {
        temp_s3_element = 0;
    }

    vec.resize(order + 1);
    spF4.resize(order + 1);
    mat.resize(order + 1);
    for (auto &mat_element : mat) {
        mat_element.resize(order + 1);
    }

    perm.resize(order + 1);
    frameCount = afGetFrameCount(afFile, AF_DEFAULT_TRACK);
    afGetRate(afFile, AF_DEFAULT_TRACK);
    data.resize(frameCount);

    dataSize = 0;
    while (afReadFrames(afFile, AF_DEFAULT_TRACK, temp_s3.data() + frameSize, frameSize)
           == static_cast<int>(frameSize)) {
        const auto temp_s3_body = vector<short>(temp_s3.begin() + frameSize, temp_s3.end());
        acvect(temp_s3_body, order, frameSize, vec);
        if (fabs(vec[0]) > thresh) {
            acmat(temp_s3_body, order, frameSize, mat);
            if (lud(mat, order, perm, &permDet) == 0) {
                lubksb(mat, order, perm, vec);
                vec[0] = 1.0;
                if (kfroma(vec, spF4, order) == 0) {
                    data[dataSize].resize(order + 1);
                    data[dataSize][0] = 1.0;

                    for (size_t i = 1; i <= order; i++) {
                        if (spF4[i] >= 1.0) {
                            spF4[i] = 0.9999999999;
                        }
                        if (spF4[i] <= -1.0) {
                            spF4[i] = -0.9999999999;
                        }
                    }

                    afromk(spF4, data[dataSize], order);
                    dataSize++;
                }
            }
        }

        for (size_t i = 0; i < frameSize; i++) {
            temp_s3[i] = temp_s3[i + frameSize];
        }
    }

    vec[0] = 1.0;
    for (size_t j = 1; j <= order; j++) {
        vec[j] = 0.0;
    }

    for (size_t i = 0; i < dataSize; i++) {
        rfroma(data[i], order, temp_s1[0]);
        for (size_t j = 1; j <= order; j++) {
            vec[j] += temp_s1[0][j];
        }
    }

    for (size_t j = 1; j <= order; j++) {
        vec[j] /= dataSize;
    }

    durbin(vec, order, spF4, temp_s1[0]);

    for (size_t j = 1; j <= order; j++) {
        if (spF4[j] >= 1.0) {
            spF4[j] = 0.9999999999;
        }
        if (spF4[j] <= -1.0) {
            spF4[j] = -0.9999999999;
        }
    }

    afromk(spF4, temp_s1[0], order);
    for (size_t curBits = 0; curBits < bits; curBits++) {
        for (size_t i = 0; i <= order; i++) {
            splitDelta[i] = 0.0;
        }
        splitDelta[order - 1] = -1.0;
        split(temp_s1, splitDelta, order, 1 << curBits, 0.01);
        refine(temp_s1, order, 1 << (curBits + 1), data, dataSize, refineIters);
    }

    npredictors = 1 << bits;
    out << order << endl << npredictors << endl;

    for (size_t i = 0; i < npredictors; i++) {
        numOverflows += write_tabledesign_codebook_entry(out, temp_s1[i], order);
    }

    if (numOverflows > 0) {
        cerr << "There was overflow - check the table" << endl;
    }

    out.close();

    return 0;
}
// End translated tabledesign.c

// aiff_extract_codebook.c translated to C++
/**
 * Create an ADPCM codebook by extracting it from an AIFF section
 */
int write_codebook(const vector<byte> &aiffData, ofstream &out) {
    s16 order = -1;
    s16 npredictors = -1;
    vector<vector<vector<s32>>> coefTable;
    size_t inputBufferPosition = 0;

    char buf[5] = { 0 };
    read_bytes_from_vec(buf, 4, 1, aiffData, &inputBufferPosition);
    if (strcmp(buf, "FORM") != 0) {
        cerr << "not an AIFF file" << endl;
        return 1;
    }
    read_bytes_from_vec(buf, 4, 1, aiffData, &inputBufferPosition);
    read_bytes_from_vec(buf, 4, 1, aiffData, &inputBufferPosition);
    if (strcmp(buf, "AIFF") != 0 && strcmp(buf, "AIFC") != 0) {
        cerr << "not an AIFF file" << endl;
        return 2;
    }

    for (;;) {
        size_t size;
        if (!read_bytes_from_vec(buf, 4, 1, aiffData, &inputBufferPosition)
            || !read_bytes_from_vec(&size, 4, 1, aiffData, &inputBufferPosition))
            break;
        BSWAP32(size);
        size_t nextOffset = inputBufferPosition + ((size + 1) & ~1);

        if (strcmp(buf, "APPL") == 0) {
            read_bytes_from_vec(buf, 4, 1, aiffData, &inputBufferPosition);
            if (strcmp(buf, "stoc") == 0) {
                u8 len;
                read_bytes_from_vec(&len, 1, 1, aiffData, &inputBufferPosition);
                if (len == 11) {
                    char chunkName[12];
                    s16 version;
                    read_bytes_from_vec(chunkName, 11, 1, aiffData, &inputBufferPosition);
                    chunkName[11] = '\0';
                    if (strcmp(chunkName, "VADPCMCODES") == 0) {
                        read_bytes_from_vec(&version, sizeof(s16), 1, aiffData, &inputBufferPosition);
                        BSWAP16(version);
                        if (version == 1) {
                            read_aifc_codebook(aiffData, &inputBufferPosition, coefTable, &order,
                                               &npredictors);
                        }
                    }
                }
            }
        }

        inputBufferPosition = nextOffset;
    }

    if (!coefTable.size()) {
        // need to call write_tabledesign_codebook()
        return 3;
    }

    out << order << endl << npredictors << endl;
    for (s32 i = 0; i < npredictors; i++) {
        for (s32 j = 0; j < order; j++) {
            for (s32 k = 0; k < 8; k++) {
                out << setw(5) << coefTable[i][k][j] << " ";
            }
            out << endl;
        }
    }

    out.close();

    return 0;
}
// End translated aiff_extract_codebook.c

// End classes

// Main Routines
vector<pair<uint32_t, uint32_t>> parse_seqfile(const vector<byte> &data, const uint16_t filetype) {

    uint16_t magic = READ_16_BITS(data, 0);
    uint16_t num_entries = READ_16_BITS(data, 2);
    assert(magic == filetype);

    size_t prev = align(4 + num_entries * 8, 16);
    vector<pair<uint32_t, uint32_t>> entries;

    for (size_t i = 0; i < num_entries; i++) {
        uint32_t offset = READ_32_BITS(data, 4 + i * 8);
        uint32_t length = READ_32_BITS(data, 8 + i * 8);

        if (filetype == TYPE_CTL) {
            assert(offset == prev);
        } else {
            assert(offset <= prev);
        }
        prev = max(prev, static_cast<size_t>(offset + length));
        entries.emplace_back(offset, length);
    }
    assert(
        all_of(data.begin() + prev, data.end(), [](byte c) { return static_cast<uint8_t>(c) == 0; }));

    return entries;
}

vector<SampleBank> parse_tbl(const vector<byte> &data,
                             const vector<pair<uint32_t, uint32_t>> &tbl_entries) {
    vector<SampleBank> banks;
    map<uint32_t, uint32_t> bank_address_to_index;
    uint32_t bank_index = 0;

    // logic described below in the comments in disassemble_sound() is implemented here; the bank_index
    // and the tbl_index, which is also the ctl_index, are both stored in each newly generated
    // SampleBank object
    for (size_t tbl_index = 0; tbl_index < tbl_entries.size(); tbl_index++) {
        uint32_t bank_address = tbl_entries[tbl_index].first, bank_size = tbl_entries[tbl_index].second;
        if (!bank_address_to_index.count(bank_address)) {
            auto bank = SampleBank(bank_index, vector<byte>(data.begin() + bank_address,
                                                            data.begin() + bank_address + bank_size));
            bank_address_to_index[bank_address] = bank_index;
            banks.push_back(bank);
            bank_index++;
        }

        for (auto &bank : banks) {
            if (bank.bank_index == bank_address_to_index[bank_address]) {
                bank.ctl_indices.push_back(tbl_index);
            }
        }
    }

    return banks;
}

int write_table(const string &filename) {
    // Load aiff
    byte i;
    vector<byte> aiff;
    auto aiffFile = ifstream(filename, ios::binary);
    if (!aiffFile) {
        cerr << "Failed to open: " << filename << "!" << endl;
        return 5;
    }
    while (aiffFile.read(reinterpret_cast<char *>(&i), sizeof(i))) {
        aiff.emplace_back(i);
    }

    // Write table
    auto tableFilename = regex_replace(filename, regex("aiff"), "table");
    auto tableFile = ofstream(tableFilename);
    if (!tableFile) {
        cerr << "Failed to open: " << tableFilename << "!" << endl;
        return 6;
    }
    auto ret = write_codebook(aiff, tableFile);
    if (!ret) {
        return 0;
    }
    ret = write_tabledesign_codebook(filename, tableFile);
    if (ret) {
        cerr << "Failed to write codebook!" << endl;
        return 7;
    }

    return 0;
}

int extract_tables(void) {
    const string extension = ".aiff";
    // TODO: pass path from other game code
    for (auto &path : fs::recursive_directory_iterator(fs::current_path())) {
        if (path.path().extension() == extension) {
            auto ret = write_table(path.path().string());
            if (ret) {
                return ret;
            }
        }
    }

    return 0;
}

int write_aiff(const AifcEntry &entry) {
    string filename = entry.filename;

    error_code err;
    if (!fs::create_directories(fs::path(filename).parent_path(), err)
        && !fs::exists(fs::path(filename).parent_path())) {
        cerr << "Failed to create directory for: " << filename << ": " << err.message() << endl;
        return 3;
    }
    auto file = ofstream(filename, ios::binary);
    if (!file) {
        cerr << "Failed to open: " << filename << "!" << endl;
        return 4;
    }
    auto writer = AiffWriter(file);
    writer.write(entry);

    return 0;
}

int extract_aiffs(const vector<byte> &rom, map<const string, const vector<uint32_t>> &seqfile_map,
                  map<const uint32_t, const string> &address_to_filename) {
    auto ctl_metadata = seqfile_map["ctl"], tbl_metadata = seqfile_map["tbl"];
    auto ctl_size = ctl_metadata[0], ctl_offset = ctl_metadata[1];
    auto tbl_size = tbl_metadata[0], tbl_offset = tbl_metadata[1];
    auto ctl_data = vector<byte>(rom.begin() + ctl_offset, rom.begin() + ctl_offset + ctl_size);
    auto tbl_data = vector<byte>(rom.begin() + tbl_offset, rom.begin() + tbl_offset + tbl_size);

    // ctl_entries and tbl_entries contain elements that were matched to each other sequentially
    // in the order they sit in their respective arrays i.e. each SampleBank needs to hold information
    // identifying what the index was of each tbl_entries element that contained a reference to it,
    // so that it can be matched to the ctl_entries elements afterward.
    // Basically stated, each "ctl_entries" element is "assigned to a sample bank" and there are more
    // of them than there are sample banks so some of them are assigned to the same sample bank.
    // An additional class could be created for this but I feel that the SampleBank class alone is
    // sufficient to store that information.
    auto tbl_entries = parse_seqfile(tbl_data, TYPE_TBL);
    auto ctl_entries = parse_seqfile(ctl_data, TYPE_CTL);
    assert(ctl_entries.size() == tbl_entries.size());

    auto banks = parse_tbl(tbl_data, tbl_entries);

    for (size_t ctl_index = 0; ctl_index < ctl_entries.size(); ctl_index++) {
        for (auto &bank : banks) {
            if (find(bank.ctl_indices.begin(), bank.ctl_indices.end(), ctl_index)
                == bank.ctl_indices.end()) {
                // here, the ctl_index is not in the ctl_indices list of the sample bank, so this sample
                // bank is not associated with this ctl_entries element This will match a single sample
                // bank only within this inner loop, but the same sample bank will be used multiple
                // times by the outer loop over all the ctl_entries, one bank for each ctl_entry
                // element, but each bank has its parse_ctl() method called multiple times, populating
                // it
                continue;
            }
            uint32_t offset = ctl_entries[ctl_index].first, length = ctl_entries[ctl_index].second;
            auto entry = vector<byte>(ctl_data.begin() + offset, ctl_data.begin() + offset + length);
            auto header = BankHeader(vector<byte>(entry.begin(), entry.begin() + 16));
            bank.parse_ctl(header, vector<byte>(entry.begin() + 16, entry.end()), address_to_filename,
                           offset);
        }
    }

    for (auto &bank : banks) {
        for (const auto &sample : bank.entries) {
            auto ret = write_aiff(sample);
            if (ret) {
                return ret;
            }
        }
    }

    return 0;
}

int extract_m64s(const vector<byte> &rom, map<const string, const vector<uint32_t>> &sequence_map) {
    for (const auto &[asset, addresses] : sequence_map) {
        uint32_t size = addresses[0], pos = addresses[1];

        auto input = vector<byte>(rom.begin() + pos, rom.begin() + pos + size);
        error_code err;
        if (!fs::create_directories(fs::path(asset).parent_path(), err)
            && !fs::exists(fs::path(asset).parent_path())) {
            cerr << "Failed to create parent directory for " << asset << ": " << err.message() << endl;
        }

        auto out = ofstream(asset, ios::binary);
        if (!out) {
            cerr << "Failed to open " << asset << "!" << endl;
            return 2;
        }
        out.write(reinterpret_cast<const char *>(input.data()), input.size());
    }

    return 0;
}

// to easily import and run this tool from a larger C++ program, main() can be renamed and called from
// an appropriate point in the larger program to extract the sound asset tree from a ROM in the current
// working directory or a directory provided by a path argument in a modified function signature.
int main(void) {
    string rom_filename = "baserom.us.z64";

    // Load ROM
    byte i;
    vector<byte> rom;
    auto file = ifstream(rom_filename, ios::binary);
    if (!file) {
        cerr << "Failed to open " << rom_filename << "!" << endl;
        return 1;
    }
    while (file.read(reinterpret_cast<char *>(&i), sizeof(i))) {
        rom.emplace_back(i);
    }

    // Extract .m64 files
    auto ret = extract_m64s(rom, sequence_map);
    if (ret) {
        cerr << "Failed to extract all m64s!" << endl;
        return ret;
    }

    // Extract .aiff files
    ret = extract_aiffs(rom, seqfile_map, sample_map);
    if (ret) {
        cerr << "Failed to extract all aiffs!" << endl;
        return ret;
    }

    // Extract .table files from all detected .aiff files
    // this includes all extended soundbank .aiff files,
    // which are external assets separate from the ROM
    ret = extract_tables();
    if (ret) {
        cerr << "Failed to extract all tables!" << endl;
        return ret;
    }

    return 0;
}