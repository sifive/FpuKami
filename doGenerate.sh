#!/bin/bash

if [ "$#" -lt  "1" ]
then
    echo -e "Usage: ./doGenerate.sh mod hardfloat-path [-s] [-c]\n"
    echo "  - mod is the name module to be compiled"
    echo "  - hardfloat-path is the path to the berkeley-hardfloat directory"
    exit 1
fi

set -x

rm tests/$1/*.v
 
make -j4

if [ "$3" != "-c" ]; then
# Generate Target.hs with $moduleName
echo "Extracting Kami code in Target.hs"
coqtop -R . FpuKami -R ../Kami/ Kami -R ../bbv/theories bbv << EOF
Require Import Kami.Extraction ModMulAdd ModFNToIN ModDivSqrt.
Definition rtlMod := getRtl (nil, (nil, $1)).
Extraction "Target.hs" RtlModule size rtlMod WriteRegFile getFins wordToNat.
Quit.
EOF
fi

rm -rf tests/$1
mkdir -p tests/$1

# Compile Kami and get into $1
echo "Compiling Kami into tests/$1/JasperTest.v"
ghc --make ../Kami/PrettyPrintVerilog.hs
../Kami/PrettyPrintVerilog > tests/$1/JasperTest.v

cd $2 && sbt -ivy .ivy2 "runMain hardfloat.Chisel3Main $1 -td $1" && cd -


# Get scala code into $1
cat $2/$1/*.v >> tests/$1/JasperTest.v

# Copy top level file into $1
cat equiv/$1/$1.sv >> tests/$1/JasperTest.v

# scp into login.sifive and run jasper, ending with opening gtkwave

# Compile the cpp file
echo "Compiling $1.cpp"
cp equiv/common.h tests/$1/.
cp equiv/$1/$1.cpp tests/$1/.
cd tests/$1

verilator -O0 --top-module JasperTest -Wno-CMPCONST -Wno-WIDTH --cc JasperTest.v --trace --trace-underscore --exe $1.cpp -Wno-fatal
echo "Running the circuit in C and dumping the output in tests/$1.log"
make -j -C obj_dir -f VJasperTest.mk VJasperTest && ./obj_dir/VJasperTest
