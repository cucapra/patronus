#!/usr/bin/env bash
#
# Compile every SystemVerilog source in this directory into a BTOR2 file
# using yosys. Run from anywhere:
#
#     ./compile.sh            # compile all *.sv next to this script
#     ./compile.sh Swap.sv    # compile a specific file
#
# Each `<name>.sv` (module `<Name>`) becomes `<name>.btor`.
#
# Requires: yosys (tested with 0.64).
#
# yosys flow, per file:
#   read_verilog -sv -formal   parse SystemVerilog, keep assert/assume props
#   write_btor                  emit BTOR2
set -euo pipefail

cd "$(dirname "$0")"

compile_one() {
    local sv="$1"
    local base="${sv%.sv}"
    # Module name is the file stem (Swap.sv -> module Swap).
    local top="$base"
    local out="${base}.btor"

    echo ">>> $sv -> $out (top: $top)"

    yosys -q -p "
        read_verilog -sv -formal ${sv};
        hierarchy -top ${top};
        proc -noopt;
        async2sync;
        flatten;
        dffunmap;
        write_btor -x ${out}
    "
}

if [[ $# -gt 0 ]]; then
    for sv in "$@"; do
        compile_one "$sv"
    done
else
    for sv in *.sv; do
        compile_one "$sv"
    done
fi

echo "Done."