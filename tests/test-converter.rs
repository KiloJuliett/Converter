use std::process::Command;
use std::str;
use test_case::test_case;

/// Asserts that the converter, run with some command, produces some output.
fn assert_converter(command: impl AsRef<str>, expected: impl AsRef<str>) {
    let output = Command::new("cargo").arg("run").arg("--")
    .args(command.as_ref().split(' ').collect::<Vec<&str>>()).output().unwrap();

    let stdout = str::from_utf8(&output.stdout).unwrap();

    assert!(
        stdout.contains(expected.as_ref()),
        "Expected: {} => {}; Output: {}",
        command.as_ref(),
        expected.as_ref(),
        stdout
    );
}

/// Tests that certain units exist and are convertible with each other.
#[test_case(vec!["s"]                                        ; "_1")]
#[test_case(vec!["m"]                                        ; "_2")]
#[test_case(vec!["kg"]                                       ; "_3")]
#[test_case(vec!["A"]                                        ; "_4")]
#[test_case(vec!["K"]                                        ; "_5")]
#[test_case(vec!["mol"]                                      ; "_6")]
#[test_case(vec!["cd"]                                       ; "_7")]
#[test_case(vec!["rad"]                               ; "_8")] // Inconsistent with the SI brochure
#[test_case(vec!["sr"]                            ; "_9")] // Inconsistent with the SI brochure
#[test_case(vec!["Hz", "s^-1"]                               ; "_10")]
#[test_case(vec!["N", "kg*m*s^-2"]                           ; "_11")]
#[test_case(vec!["Pa", "kg*m^-1*s^-2"]                       ; "_12")]
#[test_case(vec!["J", "kg*m^2*s^-2", "N*m"]                  ; "_13")]
#[test_case(vec!["W", "kg*m^2*s^-3", "J/s"]                  ; "_14")]
#[test_case(vec!["C", "A*s"]                                 ; "_15")]
#[test_case(vec!["V", "kg*m^2*s^-3*A^-1", "W/A"]             ; "_16")]
#[test_case(vec!["F", "kg^-1*m^-2*s^4*A^2", "C/V"]           ; "_17")]
#[test_case(vec!["Ω", "kg*m^2*s^-3*A^-2", "V/A"]             ; "_18")]
#[test_case(vec!["S", "kg^-1*m^-2*s^3*A^2", "A/V"]           ; "_19")]
#[test_case(vec!["Wb", "kg*m^2*s^-2*A^-1", "V*s"]            ; "_20")]
#[test_case(vec!["T", "kg*s^-2*A^-1", "Wb/m^2"]              ; "_21")]
#[test_case(vec!["H", "kg*m^2*s^-2*A^-2", "Wb/A"]            ; "_22")]
#[test_case(vec!["°C", "K"]                                  ; "_23")]
#[test_case(vec!["lm", "cd*sr"]                              ; "_24")]
#[test_case(vec!["lx", "cd*sr*m^-2", "lm/m^2"]               ; "_25")]
#[test_case(vec!["Bq", "s^-1"]                               ; "_26")]
#[test_case(vec!["Gy", "m^2*s^-2", "J/kg"]                   ; "_27")]
#[test_case(vec!["Sv", "m^2*s^-2", "J/kg"]                   ; "_28")]
#[test_case(vec!["kat", "mol*s^-1"]                          ; "_29")]
#[test_case(vec!["m^2"]                                      ; "_30")]
#[test_case(vec!["m^3"]                                      ; "_31")]
#[test_case(vec!["m*s^-1"]                                   ; "_32")]
#[test_case(vec!["m*s^-2"]                                   ; "_33")]
#[test_case(vec!["m^-1"]                                     ; "_34")]
#[test_case(vec!["kg*m^-3"]                                  ; "_35")]
#[test_case(vec!["kg*m^-2"]                                  ; "_36")]
#[test_case(vec!["m^3*kg^-1"]                                ; "_37")]
#[test_case(vec!["A*m^-2"]                                   ; "_38")]
#[test_case(vec!["A*m^-1"]                                   ; "_39")]
#[test_case(vec!["mol*m^-3"]                                 ; "_40")]
#[test_case(vec!["kg*m^-3"]                                  ; "_41")]
#[test_case(vec!["cd*m^-2"]                                  ; "_42")]
#[test_case(vec!["Pa*s", "kg*m^-1*s^-1"]                     ; "_43")]
#[test_case(vec!["N*m", "kg*m^2*s^-2"]                       ; "_44")]
#[test_case(vec!["N*m^-1", "kg*s^-2"]                        ; "_45")]
#[test_case(vec!["rad*s^-1"]                         ; "_46")] // Inconsistent with the SI brochure
#[test_case(vec!["rad*s^-2"]                         ; "_47")] // Inconsistent with the SI brochure
#[test_case(vec!["W*m^-2", "kg*s^-3"]                        ; "_48")]
#[test_case(vec!["J*K^-1", "kg*m^2*s^-2*K^-1"]               ; "_49")]
#[test_case(vec!["J*K^-1*kg^-1", "m^2*s^-2*K^-1"]           ; "_50")]
#[test_case(vec!["J*kg^-1", "m^2*s^-2"]                      ; "_51")]
#[test_case(vec!["W*m^-1*K^-1", "kg*m*s^-3*K^-1"]            ; "_52")]
#[test_case(vec!["J*m^-3", "kg*m^-1*s^-2"]                   ; "_53")]
#[test_case(vec!["V*m^-1", "kg*m*s^-3*A^-1"]                 ; "_54")]
#[test_case(vec!["C*m^-3", "A*s*m^-3"]                       ; "_55")]
#[test_case(vec!["C*m^-2", "A*s*m^-2"]                       ; "_56")]
#[test_case(vec!["C*m^-2", "A*s*m^-2"]                       ; "_57")]
#[test_case(vec!["F*m^-1", "kg^-1*m^-3*s^4*A^2"]             ; "_58")]
#[test_case(vec!["H*m^-1", "kg*m*s^-2*A^-2"]                 ; "_59")]
#[test_case(vec!["J*mol^-1", "kg*m^2*s^-2*mol^-1"]           ; "_60")]
#[test_case(vec!["J*K^-1*mol^-1", "kg*m^2*s^-2*mol^-1*K^-1"] ; "_61")]
#[test_case(vec!["C*kg^-1", "A*s*kg^-1"]                     ; "_62")]
#[test_case(vec!["Gy*s^-1", "m^2*s^-3"]                      ; "_63")]
// #[test_case(vec!["W*sr^-1", "kg*m^2*s^-3"]                   ; "_64")]
// #[test_case(vec!["W*sr^-1*m^-2", "kg*s^-3"]                  ; "_65")]
#[test_case(vec!["kat*m^-3", "mol*s^-1*m^-3"]                ; "_66")]
// #[test_case(vec![""]                                         ; "_67")]
// #[test_case(vec![""]                                         ; "_68")]
// #[test_case(vec![""]                                         ; "_69")]
// #[test_case(vec![""]                                         ; "_70")]
// #[test_case(vec![""]                                         ; "_71")]
// #[test_case(vec![""]                                         ; "_72")]
// #[test_case(vec![""]                                         ; "_73")]
// #[test_case(vec![""]                                         ; "_74")]
// #[test_case(vec![""]                                         ; "_75")]
// #[test_case(vec![""]                                         ; "_76")]
// #[test_case(vec![""]                                         ; "_77")]
// #[test_case(vec![""]                                         ; "_78")]
// #[test_case(vec![""]                                         ; "_79")]
// #[test_case(vec![""]                                         ; "_80")]
// #[test_case(vec![""]                                         ; "_81")]
// #[test_case(vec![""]                                         ; "_82")]
// #[test_case(vec![""]                                         ; "_83")]
// #[test_case(vec![""]                                         ; "_84")]
// #[test_case(vec![""]                                         ; "_85")]
// #[test_case(vec![""]                                         ; "_86")]
// #[test_case(vec![""]                                         ; "_87")]
// #[test_case(vec![""]                                         ; "_88")]
// #[test_case(vec![""]                                         ; "_89")]
// #[test_case(vec![""]                                         ; "_90")]
// #[test_case(vec![""]                                         ; "_91")]
// #[test_case(vec![""]                                         ; "_92")]
// #[test_case(vec![""]                                         ; "_93")]
// #[test_case(vec![""]                                         ; "_94")]
// #[test_case(vec![""]                                         ; "_95")]
// #[test_case(vec![""]                                         ; "_96")]
// #[test_case(vec![""]                                         ; "_97")]
// #[test_case(vec![""]                                         ; "_98")]
// #[test_case(vec![""]                                         ; "_99")]
// #[test_case(vec![""]                                         ; "_100")]
// #[test_case(vec![""]                                         ; "_101")]
// #[test_case(vec![""]                                         ; "_102")]
// #[test_case(vec![""]                                         ; "_103")]
// #[test_case(vec![""]                                         ; "_104")]
// #[test_case(vec![""]                                         ; "_105")]
// #[test_case(vec![""]                                         ; "_106")]
// #[test_case(vec![""]                                         ; "_107")]
// #[test_case(vec![""]                                         ; "_108")]
// #[test_case(vec![""]                                         ; "_109")]
// #[test_case(vec![""]                                         ; "_110")]
fn test_unit_existence(symbols: Vec<&str>) {
    let symbol_reference = symbols[0];

    for symbol in symbols {
        let command = format!("1 {} to {}", symbol_reference, symbol);
        let expected = symbol;

        assert_converter(command, expected);
    }
}

#[test_case("1000 m to km"   , "1 km"       ; "_1")]
#[test_case("1 m to km"      , "1/1000 km"  ; "_2")]
#[test_case("pi rad to °"    , "180 °"      ; "_3")]
#[test_case("45 ° to rad"    , "π/4 rad"    ; "_4")]
#[test_case("1 L to m3"      , "1/1000 m3"  ; "_5")]
#[test_case("1 L to m^3"     , "1/1000 m^3" ; "_6")]
#[test_case("1 m³ to l"      , "1000 l"     ; "_7")]
#[test_case("100 kPa to MPa" , "1/10 MPa"   ; "_8")]
fn test_converter(command: &str, expected: &str) {
    assert_converter(command, expected);
}
