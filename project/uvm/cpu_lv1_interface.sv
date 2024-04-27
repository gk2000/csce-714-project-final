//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_lv1_interface.sv
// Description: Basic CPU-LV1 interface with assertions
// Designers: Venky & Suru
//=====================================================================


interface cpu_lv1_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1           = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1           = `ADDR_WID_LV1       ;

    reg   [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1_reg    ;

    wire  [DATA_WID_LV1 - 1   : 0] data_bus_cpu_lv1        ;
    logic [ADDR_WID_LV1 - 1   : 0] addr_bus_cpu_lv1        ;
    logic                          cpu_rd                  ;
    logic                          cpu_wr                  ;
    logic                          cpu_wr_done             ;
    logic                          data_in_bus_cpu_lv1     ;

    assign data_bus_cpu_lv1 = data_bus_cpu_lv1_reg ;

//Assertions
//ASSERTION1: cpu_wr and cpu_rd should not be asserted at the same clock cycle
    property prop_simult_cpu_wr_rd;
        @(posedge clk)
          not(cpu_rd && cpu_wr);
    endproperty

    assert_simult_cpu_wr_rd: assert property (prop_simult_cpu_wr_rd)
    else
        `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_simult_cpu_wr_rd Failed: cpu_wr and cpu_rd asserted simultaneously"))

//Done: Add assertions at this interface

    //ASSERTION 2: Address should not be invalid when Rd/Wr request is processed
    property valid_addr_rd_wr;
        @(posedge clk)
            (cpu_rd || cpu_wr) |-> (addr_bus_cpu_lv1[31:0] !== 32'bx);
    endproperty

    assert_valid_addr_rd_wr: assert property (valid_addr_rd_wr)
    else
        `uvm_error("cpu_lv1_interface", "Assertion valid_addr_rd_wr failed: Address is X when Rd/Wr command is issued")

    //ASSERTION 3: cpu_rd should be followed by data_in_bus_cpu_lv1 and both should be deasserted acc to HAS
    property valid_rd_txn;
        @(posedge clk)
        cpu_rd |=> ##[0:$] data_in_bus_cpu_lv1 ##1 !cpu_rd ##1 !data_in_bus_cpu_lv1 ;
    endproperty

    assert_valid_rd_txn: assert property (valid_rd_txn)
    else
        `uvm_error("cpu_lv1_interface", "Assertion valid_rd_txn failed: cpu_rd=>data_in_bus_cpu_lv1=>!cpu_rd=>!data_in_bus_cpu_lv1 sequence is not followed")

    //ASSERTION 4: If data_in_bus_cpu_lv1 is asserted, cpu_rd should be high
    property valid_data_in_bus_rd;
        @(posedge clk)
        $rose(data_in_bus_cpu_lv1) |-> cpu_rd;
    endproperty
    assert_valid_data_in_bus_rd: assert property (valid_data_in_bus_rd)
    else
        `uvm_error("cpu_lv1_interface", "Assertion valid_data_in_bus_rd failed: cpu_rd not high when data_in_bus_cpu_lv1 asserted")

    //ASSERTION 5: If cpu_wr is high, cpu_wr_done should be high within timeout
    property valid_cpu_wr_done;
         @(posedge clk)
         cpu_wr |-> ##[1:109] cpu_wr_done;
    endproperty
 
    assert_valid_cpu_wr_done: assert property (valid_cpu_wr_done)
    else
        `uvm_error("cpu_lv1_interface", "Assertion valid_cpu_wr_done failed: cpu_wr done")

    //ASSERTION 6: If cpu_rd is high, cpu_rd should be low within timeout
    property valid_cpu_rd;
        @(posedge clk)
        cpu_rd |-> ##[1:109] !cpu_rd;
   endproperty

   assert_valid_cpu_rd: assert property (valid_cpu_rd)
   else
       `uvm_error("cpu_lv1_interface", "Assertion valid_cpu_rd failed: cpu_rd didn't go low before timeout")

   //ASSERTION 7: When cpu_wr_done goes high, cpu_wr should go low after one clock cycle.
    property prop_deassert_cpu_wr_after_write;
        @(posedge clk)
            cpu_wr_done |=> !cpu_wr;
    endproperty

    deassert_cpu_wr_after_write: assert property(prop_deassert_cpu_wr_after_write)
    else
    `uvm_error("cpu_lv1_interface",$sformatf("Assertion deassert_cpu_wr_after_write Failed: cpu_wr not deasserted after writing is done"))

    //ASSERTION 8: No writes to the instruction cache
    property prop_assert_no_write_on_icache;
        @(posedge clk)
         cpu_wr |-> addr_bus_cpu_lv1 >= 32'h4000_0000;
     endproperty
 
     assert_no_write_on_icache: assert property(prop_assert_no_write_on_icache)
     else 
     `uvm_error("cpu_lv1_interface",$sformatf("Assertion assert_no_write_on_icache Failed: illegal write to Icache"))

endinterface
