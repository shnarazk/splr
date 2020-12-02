use std::{
    env,
    fs::{self, File},
    path::PathBuf,
    process::{Command, Stdio},
};

/*
for f in ${UUF250}*.cnf; do
    target=`basename -s .cnf $f`
    rm -f ${target}.out
    splr -c -p ${target}.out ${f} > /dev/null
    if [ -z ${target}.out ]; then
        echo ' FAIL TO CERTIFICATE: ${f}'
        exit 1;
    egrep -v '^[cs]' < ${target}.out > ${target}.drat
    gratgen ${f} ${target}.drat -o ${target}.grat -j 4 > /dev/null
    gratchk unsat ${f} ${target}.grat
*/

fn main() {
    if let Some(uuf250) = env::args().nth(1) {
        let path = PathBuf::from(uuf250);
        for e in path.read_dir().expect(&format!("not exist {:?}", path)) {
            if let Ok(cnf) = e.map(|e| e.path()) {
                if let Some(target) = cnf.file_name().map(PathBuf::from) {
                    let out = target.with_extension("out");
                    let drat = target.with_extension("drat");
                    let grat = target.with_extension("grat");
                    // println!("########################################");
                    print!("# {}", cnf.file_name().unwrap().to_string_lossy());
                    // rm -f ${target}.out
                    if out.exists() {
                        fs::remove_file(&out).expect("fail to rm");
                    }
                    // splr -c -p ${target}.out ${f} > /dev/null
                    Command::new("splr")
                        .args(&["-c", "-p", &*out.to_string_lossy(), &*cnf.to_string_lossy()])
                        .stdout(Stdio::null())
                        .output()
                        .expect("failed to execute Splr");
                    // if [ -z ${target}.out ]; then
                    //     echo ' FAIL TO CERTIFICATE: ${f}'
                    //     exit 1;
                    // fi
                    if !out.exists() {
                        panic!(format!(
                            " FAIL TO CERTIFICATE: {} => {}",
                            cnf.file_name().unwrap().to_string_lossy(),
                            out.to_string_lossy(),
                        ));
                    }
                    // egrep -v '^[cs]' < ${target}.out > ${target}.drat
                    Command::new("egrep")
                        .args(&["-v", "^[cs]"])
                        .stdin(File::open(out).expect(""))
                        .stdout(File::create(&drat).expect(""))
                        .output()
                        .expect("");
                    // gratgen ${f} ${target}.drat -o ${target}.grat -j 4 > /dev/null
                    Command::new("gratgen")
                        .args(&[
                            &*cnf.to_string_lossy(),
                            &*drat.to_string_lossy(),
                            "-o",
                            &*grat.to_string_lossy(),
                            "-j",
                            "4",
                        ])
                        .stdin(Stdio::piped())
                        .stdout(Stdio::null())
                        .stderr(Stdio::null())
                        .output()
                        .unwrap();
                    // .expect(&format!("FAIL TO GENERATE: {} => {}",
                    //                 cnf.file_name().unwrap().to_string_lossy(),
                    //                 grat.to_string_lossy(),
                    // ));
                    // gratchk unsat ${f} ${target}.grat
                    if grat.exists() {
                        print!(" => {}", grat.to_string_lossy());
                    } else {
                        panic!(format!(
                            " FAIL TO CONVERT: {} => {}",
                            cnf.file_name().unwrap().to_string_lossy(),
                            grat.to_string_lossy(),
                        ));
                    }
                    let mut pass = false;
                    if let Ok(out) = Command::new("gratchk")
                        .args(&["unsat", &*cnf.to_string_lossy(), &*grat.to_string_lossy()])
                        .stdin(Stdio::piped())
                        .stderr(Stdio::null())
                        .output()
                    {
                        let str = String::from_utf8_lossy(&out.stdout);
                        for l in (*str).split('\n') {
                            if l.contains(&"s VERIFIED UNSAT") {
                                pass = true;
                                println!(" => VERIFIED UNSAT");
                                break;
                            }
                        }
                    }
                    if !pass {
                        panic!(format!(
                            " FAIL TO CERTIFICATE: {} => {}",
                            cnf.file_name().unwrap().to_string_lossy(),
                            grat.to_string_lossy(),
                        ));
                    }
                }
            }
        }
    }
}
