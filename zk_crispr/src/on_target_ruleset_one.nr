// Have a global scale
// Have a position scale that is smaller, try /5 and scale the value by that for negative numbers

global SCALE:Field = 10000000; // 10^7
global POSITION_SCALE:Field =2000000; // something smaller than scale

global INTERCEPT:Field = 10597636;

global GC_LOW:Field = 202625;
global GC_HIGH:Field = 166587;


// final_score = 1 / (1 + e^(-raw_score))
// mul SCALE plus 10000000

// greater or equal to 0.60
global HIGH_THRESHOLD:u64 = 10405465;

// greater or equal to 0.50
global GOOD_THRESHOLD:u64 = 10000000;

// greater or equal to 0.30
global MED_THRESHOLD:u64 = 9594535;


pub fn on_target_ruleset_one_score(seq: [Field; 30]) -> [Field; 4] {
    // check PAM is AGG
    let pam_check = (seq[25] == 2)  & (seq[26] == 2);
    //assert(seq[25] == 2);
    //assert(seq[26] == 2);

    let mut score = INTERCEPT;

    //println(f"The init score is {score}");

    let mut gc_count = 0;
    for i in 4..24 {
        if seq[i] == 2 {
            gc_count += 1;
        }
        if seq[i] == 1 {
            gc_count += 1;
        }
    }
    //println(f"gc_count is {gc_count}");

    if gc_count < 10 {
        score -=(10- gc_count as Field)*GC_LOW;
    }
    if gc_count > 10 {
        score -=(gc_count as Field - 10)*GC_HIGH;
    }

    let score_u64 = score as u64;
    //println(f"The after gc, score_u64 is {score_u64}");

    let mut position_feature_sc = 0;
    let mut successful_ifs = 0;
    // Single letter features (lines 3-41)
    if seq[1] == 2 {
        position_feature_sc += 1724623;
        successful_ifs +=1;
    }
    if seq[2] == 0 {
        position_feature_sc += 1676113;
        successful_ifs +=1;
    }
    if seq[2] == 1 {
        position_feature_sc += 2172128;
        successful_ifs +=1;
    }
    if seq[3] == 1 {
        position_feature_sc += 1899334;
        successful_ifs +=1;
    }
    if seq[4] == 1 {
        position_feature_sc += 1798198;
        successful_ifs +=1;
    }
    if seq[4] == 2 {
        position_feature_sc += 2245956;
        successful_ifs +=1;
    }
    if seq[5] == 0 {
        position_feature_sc += 2036440;
        successful_ifs +=1;
    }
    if seq[5] == 1 {
        position_feature_sc += 2098376;
        successful_ifs +=1;
    }
    if seq[6] == 1 {
        position_feature_sc += 1258819;
        successful_ifs +=1;
    }
    if seq[6] == 2 {
        position_feature_sc += 1606736;
        successful_ifs +=1;
    }
    if seq[11] == 0 {
        position_feature_sc += 1533901;
        successful_ifs +=1;
    }
    if seq[14] == 0 {
        position_feature_sc += 2085376;
        successful_ifs +=1;
    }
    if seq[14] == 1 {
        position_feature_sc += 1986187;
        successful_ifs +=1;
    }
    if seq[15] == 0 {
        position_feature_sc += 2272620;
        successful_ifs +=1;
    }
    if seq[15] == 1 {
        position_feature_sc += 1880978;
        successful_ifs +=1;
    }
    if seq[15] == 3 {
        position_feature_sc += 1714056;
        successful_ifs +=1;
    }
    if seq[16] == 0 {
        position_feature_sc += 2097454;
        successful_ifs +=1;
    }
    if seq[16] == 2 {
        position_feature_sc += 1824454;
        successful_ifs +=1;
    }
    if seq[17] == 1 {
        position_feature_sc += 1654205;
        successful_ifs +=1;
    }
    if seq[17] == 2 {
        position_feature_sc += 1321904;
        successful_ifs +=1;
    }
    if seq[18] == 0 {
        position_feature_sc += 2225089;
        successful_ifs +=1;
    }
    if seq[18] == 1 {
        position_feature_sc += 1492206;
        successful_ifs +=1;
    }
    if seq[19] == 2 {
        position_feature_sc += 1582627;
        successful_ifs +=1;
    }
    if seq[19] == 3 {
        position_feature_sc += 1945694;
        successful_ifs +=1;
    }
    if seq[20] == 2 {
        position_feature_sc += 2379899;
        successful_ifs +=1;
    }
    if seq[20] == 3 {
        position_feature_sc += 1909288;
        successful_ifs +=1;
    }
    if seq[21] == 1 {
        position_feature_sc += 2057823;
        successful_ifs +=1;
    }
    if seq[21] == 3 {
        position_feature_sc += 1469433;
        successful_ifs +=1;
    }
    if seq[22] == 3 {
        position_feature_sc += 1122993;
        successful_ifs +=1;
    }
    if seq[23] == 1 {
        position_feature_sc += 1123765;
        successful_ifs +=1;
    }
    if seq[23] == 2 {
        position_feature_sc += 2278916;
        successful_ifs +=1;
    }
    if seq[23] == 3 {
        position_feature_sc += 1596898;
        successful_ifs +=1;
    }
    if seq[24] == 0 {
        position_feature_sc += 1922700;
        successful_ifs +=1;
    }
    if seq[24] == 1 {
        position_feature_sc += 2287935;
        successful_ifs +=1;
    }
    if seq[24] == 3 {
        position_feature_sc += 1778363;
        successful_ifs +=1;
    }
    if seq[27] == 2 {
        position_feature_sc += 1310984;
        successful_ifs +=1;
    }
    if seq[27] == 3 {
        position_feature_sc += 2117877;
        successful_ifs +=1;
    }
    if seq[28] == 1 {
        position_feature_sc += 1839555;
        successful_ifs +=1;
    }
    if seq[29] == 2 {
        position_feature_sc += 2386342;
        successful_ifs +=1;
    }

    // Two letter features (lines 42-72)
    if (seq[1] == 2) & (seq[2] == 3) {
        position_feature_sc += 1374222;
        successful_ifs +=1;
    }
    if (seq[4] == 2) & (seq[5] == 1) {
        position_feature_sc += 2300043;
        successful_ifs +=1;
    }
    if (seq[5] == 0) & (seq[6] == 0) {
        position_feature_sc += 1165164;
        successful_ifs +=1;
    }
    if (seq[5] == 3) & (seq[6] == 0) {
        position_feature_sc += 2760627;
        successful_ifs +=1;
    }
    if (seq[6] == 2) & (seq[7] == 2) {
        position_feature_sc += 1509184;
        successful_ifs +=1;
    }
    if (seq[11] == 2) & (seq[12] == 2) {
        position_feature_sc += 483093;
        successful_ifs +=1;
    }
    if (seq[11] == 3) & (seq[12] == 0) {
        position_feature_sc += 2709261;
        successful_ifs +=1;
    }
    if (seq[11] == 3) & (seq[12] == 1) {
        position_feature_sc += 2496298;
        successful_ifs +=1;
    }
    if (seq[11] == 3) & (seq[12] == 3) {
        position_feature_sc += 1413127;
        successful_ifs +=1;
    }
    if (seq[12] == 2) & (seq[13] == 2) {
        position_feature_sc += 1665437;
        successful_ifs +=1;
    }
    if (seq[13] == 2) & (seq[14] == 0) {
        position_feature_sc += 2763849;
        successful_ifs +=1;
    }
    if (seq[13] == 2) & (seq[14] == 1) {
        position_feature_sc += 1462975;
        successful_ifs +=1;
    }
    if (seq[16] == 3) & (seq[17] == 2) {
        position_feature_sc += 1201854;
        successful_ifs +=1;
    }
    if (seq[18] == 2) & (seq[19] == 2) {
        position_feature_sc += 1333192;
        successful_ifs +=1;
    }
    if (seq[18] == 3) & (seq[19] == 1) {
        position_feature_sc += 2353183;
        successful_ifs +=1;
    }
    if (seq[19] == 1) & (seq[20] == 1) {
        position_feature_sc += 2748072;
        successful_ifs +=1;
    }
    if (seq[19] == 3) & (seq[20] == 2) {
        position_feature_sc += 1632734;
        successful_ifs +=1;
    }
    if (seq[20] == 0) & (seq[21] == 1) {
        position_feature_sc += 2568209;
        successful_ifs +=1;
    }
    if (seq[20] == 1) & (seq[21] == 2) {
        position_feature_sc += 2329072;
        successful_ifs +=1;
    }
    if (seq[20] == 2) & (seq[21] == 0) {
        position_feature_sc += 1163544;
        successful_ifs +=1;
    }
    if (seq[20] == 2) & (seq[21] == 2) {
        position_feature_sc += 1217793;
        successful_ifs +=1;
    }
    if (seq[21] == 3) & (seq[22] == 1) {
        position_feature_sc += 970308;
        successful_ifs +=1;
    }
    if (seq[22] == 1) & (seq[23] == 2) {
        position_feature_sc += 2856197;
        successful_ifs +=1;
    }
    if (seq[22] == 1) & (seq[23] == 3) {
        position_feature_sc += 1536793;
        successful_ifs +=1;
    }
    if (seq[23] == 0) & (seq[24] == 0) {
        position_feature_sc += 1420508;
        successful_ifs +=1;
    }
    if (seq[23] == 0) & (seq[24] == 2) {
        position_feature_sc += 2649075;
        successful_ifs +=1;
    }
    if (seq[24] == 0) & (seq[25] == 2) {
        position_feature_sc += 1922700;
        successful_ifs +=1;
    }
    if (seq[24] == 1) & (seq[25] == 2) {
        position_feature_sc += 2287935;
        successful_ifs +=1;
    }
    if (seq[24] == 3) & (seq[25] == 2) {
        position_feature_sc += 1778363;
        successful_ifs +=1;
    }
    if (seq[26] == 2) & (seq[27] == 3) {
        position_feature_sc += 2117877;
        successful_ifs +=1;
    }
    if (seq[28] == 2) & (seq[29] == 2) {
        position_feature_sc += 1302260;
        successful_ifs +=1;
    }
    let position_feature_sc_u64 = position_feature_sc as u64;
    //println(f"The position_feature_sc_u64 is {position_feature_sc_u64}");

    if successful_ifs > 0 {
        position_feature_sc = position_feature_sc -POSITION_SCALE*((successful_ifs-1) as Field);
    }


    let position_feature_sc_u64 = position_feature_sc as u64;
    //println(f"The position_feature_sc_u64 is {position_feature_sc_u64}");

    score += position_feature_sc;

    if successful_ifs > 0 {
        score -= POSITION_SCALE;
    }

    let score_u64 = score as u64;
    //println(f"The pre score is {score_u64}");

    if !pam_check {
        //println(f"PAM check failed");
        score = 0;
    }

    let score_u64 = score as u64;

    let mut eff_arr: [Field; 4] = [0;4];
    if score_u64 > HIGH_THRESHOLD {
        //println(f"High efficiency");
        eff_arr[0] = 1;
    } else if score_u64 > GOOD_THRESHOLD {
        //println(f"Good efficiency");
        eff_arr[1] = 1;
    } else if score_u64 >= MED_THRESHOLD {
        //println(f"Medium efficiency");
        eff_arr[2] = 1;
    } else {
        //println(f"Low efficiency");
        eff_arr[3] = 1;
    }

    eff_arr
}

#[test]
fn test_main() {
    on_target_ruleset_one_score([0;30]);

    // Uncomment to make test fail
    // main(1, 1);
}
