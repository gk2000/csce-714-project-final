//=====================================================================
// Project: 4 core MESI cache design
// File Name: test_lib.svh
// Description: Base test class and list of tests
// Designers: Venky & Suru
//=====================================================================
//TODO: add your testcase files in here
`include "base_test.sv"
`include "read_miss_icache.sv"
`include "write_read.sv"
`include "read_miss_dcache.sv"
`include "multiple_write_same_block.sv"
`include "multiple_read_same_block.sv"
`include "four_writes_one_read.sv"
`include "simultaneous_write.sv"
`include "completely_random_simultaneous.sv"
`include "random_writes.sv"
`include "random_reads.sv"
`include "all_cores_read_snoop.sv"
`include "random_write_read.sv"