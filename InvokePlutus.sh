#! /bin/bash
# execute Printer.v and run the generated .pir file through the plutus compiler
# this script depends on direct paths to the Plinth CLI tool
out=./output/test.pir
plutus_path=../plutus/plutus
make
echo -e "\033[0;34mpir output:\033[0m"
cat ${out}
echo -e "\n"
mkdir -p ${plutus_path}/input
cp ${out} ${plutus_path}/input
cd ${plutus_path}
# assumes the plutus executable has been built in the past
nix develop --command bash -c 'cabal exec -- plutus input/test.pir -o input/test.plc && echo -e "\n\033[0;33mplc output:\033[0m" && cat input/test.plc && echo -e "\n"'
