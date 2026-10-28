#!/bin/bash


# define full set of tests, pair to a list of slugs for the test files

# NOTE keccak original is not included in either yet


ALL=( "mux" "i2c" "axis-fifo-wrap" "axis-adapter" "axis_frame_len" "axis-fifo.original" "zipcpu_sdspi" "axis-frame-fifo" "axis-switch" "axis-async-fifo" "axi-lite-xlnx" "axi-stream-xlnx")

JIT=("mux" "i2c" "axis-adapter" "axis_frame_len" "axis-switch" "axi-lite-xlnx" "axi-stream-xlnx")

INTERP=("${ALL[@]}")

build_args="--release"

return_code=0

function run_tests() {
  local -n li=$1
  local -n sim_args=$2
  
  for t_name in ${li[@]}
    do
      echo "$t_name"

      # because filenames and testnames aren't always uniform, use find to obtain them
      design_file=$(find inputs/repair -name "${t_name}*.btor")
      tb_files=$(find inputs/repair -name "${t_name}*.csv")

      
      for tb in ${tb_files[@]}
      do
        cargo run $build_args -p sim -- --init=zero $sim_args --testbench=$tb $design_file
        if [ $? -ne 0 ]; then
          return_code+=1
        fi
      done
    done
}



if [ $1 = "jit" ]; then
  args="--use-jit"
  run_tests JIT args
else
  run_tests INTERP args
fi

exit $return_code
