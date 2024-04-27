//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_interface.sv
// Description: Basic system bus interface including arbiter
// Designers: Venky & Suru
//=====================================================================

interface system_bus_interface(input clk);

    import uvm_pkg::*;
    `include "uvm_macros.svh"

    parameter DATA_WID_LV1        = `DATA_WID_LV1       ;
    parameter ADDR_WID_LV1        = `ADDR_WID_LV1       ;
    parameter NO_OF_CORE            = 4;

    wire [DATA_WID_LV1 - 1 : 0] data_bus_lv1_lv2     ;
    wire [ADDR_WID_LV1 - 1 : 0] addr_bus_lv1_lv2     ;
    wire                        bus_rd               ;
    wire                        bus_rdx              ;
    wire                        lv2_rd               ;
    wire                        lv2_wr               ;
    wire                        lv2_wr_done          ;
    wire                        cp_in_cache          ;
    wire                        data_in_bus_lv1_lv2  ;

    wire                        shared               ;
    wire                        all_invalidation_done;
    wire                        invalidate           ;

    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_proc ;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_gnt_snoop;
    logic [NO_OF_CORE - 1  : 0]   bus_lv1_lv2_req_snoop;
    logic                       bus_lv1_lv2_gnt_lv2  ;
    logic                       bus_lv1_lv2_req_lv2  ;

//Assertions
//property that checks that signal_1 is asserted in the previous cycle of signal_2 assertion
    property prop_sig1_before_sig2(signal_1,signal_2);
    @(posedge clk)
        signal_2 |-> $past(signal_1);
    endproperty

//ASSERTION1: lv2_wr_done should not be asserted without lv2_wr being asserted in previous cycle
    assert_lv2_wr_done: assert property (prop_sig1_before_sig2(lv2_wr,lv2_wr_done))
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_lv2_wr_done Failed: lv2_wr not asserted before lv2_wr_done goes high"))

//ASSERTION2: data_in_bus_lv1_lv2 and cp_in_cache should not be asserted without lv2_rd being asserted in previous cycle

assert_read_response: assert property (prop_sig1_before_sig2(lv2_rd,{data_in_bus_lv1_lv2|cp_in_cache}))
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion assert_read_response Failed: lv2_rd not asserted before either data_in_bus_lv1_lv2 or cp_in_cache goes high "))



//Done: Add assertions at this interface
//There are atleast 20 such assertions. Add as many as you can!!

    //ASSERTION 3: lv2_rd should be followed by data_in_bus_lv1_lv2 and both should be deasserted acc to HAS
    property valid_lv2_rd_txn;
        @(posedge clk)
        lv2_rd |=> ##[0:$] data_in_bus_lv1_lv2 ##1 !lv2_rd ;
    endproperty

    assert_valid_lv2_rd_txn: assert property (valid_lv2_rd_txn)
    else
        `uvm_error("system_bus_interface", "Assertion valid_lv2_rd_txn failed: lv2_rd=>data_in_bus_lv1_lv2=>!lv2_rd sequence is not followed")

    //ASSERTION 4: If data_in_bus_lv1_lv2 is asserted, lv2_rd should be high
    property valid_data_in_lv2_bus_rd;
        @(posedge clk)
        (data_in_bus_lv1_lv2===1'bz) ##1 (data_in_bus_lv1_lv2==1'b1) |-> lv2_rd;
    endproperty

    assert_valid_data_in_lv2_bus_rd: assert property (valid_data_in_lv2_bus_rd)
    else
        `uvm_error("system_bus_interface", "Assertion valid_data_in_lv2_bus_rd failed: lv2_rd not high when data_in_bus_lv1_lv2 asserted")

    //ASSERTION 5: lv2_wr should be followed by lv2_wr_done and both should be deasserted acc to HAS
    property valid_lv2_wr_txn;
        @(posedge clk)
        lv2_wr |=> ##[0:$] lv2_wr_done ##1 !lv2_wr ##1 !lv2_wr_done ;
    endproperty

    assert_valid_lv2_wr_txn: assert property (valid_lv2_wr_txn)
    else
        `uvm_error("system_bus_interface", "Assertion valid_lv2_wr_txn failed: lv2_wr=>lv2_wr_done=>!lv2_wr=>!lv2_wr_done sequence is not followed")

    //ASSERTION 6: If bus_rd or bus_rdx is high, lv2_rd has to be high
    property valid_bus_rd_txn;
        @(posedge clk)
        bus_rd|bus_rdx |-> lv2_rd ;
    endproperty

    assert_valid_bus_rd_txn: assert property (valid_bus_rd_txn)
    else
        `uvm_error("system_bus_interface", "Assertion valid_bus_rd_txn failed: bus_rd or bus_rdx is high without lv2_rd")

    //ASSERTION 7: Processor grant can be given to a max of one processor core at any time
    property proc_grant_onehot;
        @(posedge clk)
            $onehot0(bus_lv1_lv2_gnt_proc);
    endproperty
    proc_grant_onehot_label: assert property(proc_grant_onehot)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion proc_grant_onehot Failed: Processor grant granted for more than core simultaneously"))

    //ASSERTION 8: When data_in_bus_lv1_lv2 goes high, lv2_rd should go low after one cycle
    property prop_deassert_lv2_rd_after_lv2_read;
        @(posedge clk)
            data_in_bus_lv1_lv2 |=> !lv2_rd;
    endproperty
    deassert_lv2_rd_after_lv2_read: assert property(prop_deassert_lv2_rd_after_lv2_read)
    else
        `uvm_error("system_bus_interface",$sformatf("Assertion deassert_lv2_rd_after_lv2_read Failed: lv2_rd not deasserted after level 2 data is put on bus "))

    //ASSERTION 9: Processor request has to be high before processor grant can be made high
    property gnt_proc_to_be_followed_by_req_proc;
        @(posedge clk)
            (bus_lv1_lv2_gnt_proc[0]) |-> $past(bus_lv1_lv2_req_proc[0]);
    endproperty
    gnt_proc_req_proc_label: assert property(gnt_proc_to_be_followed_by_req_proc)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_proc_to_be_followed_by_req_proc failed core 0: grant granted before request"))

    //ASSERTION 10: Snoop request has to be high before snoop grant can be high
    property gnt_bus_to_be_followed_by_req_bus;
        @(posedge clk)
            (bus_lv1_lv2_gnt_snoop[0]) |-> $past(bus_lv1_lv2_req_snoop[0]);
    endproperty
    gnt_bus_req_bus_label: assert property(gnt_bus_to_be_followed_by_req_bus)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_bus_to_be_followed_by_req_bus failed core 0: grant granted before request"))

    // //ASSERTION 11: In case of read in shared/modified states, when data_in_bus_lv1_lv2 goes high, bus_rd should go low after one clock cycle
    // property prop_deassert_bus_rd_after_read;
    //     @(posedge clk)
    //         data_in_bus_lv1_lv2 |=> !bus_rd;
    // endproperty
    // deassert_bus_rd_after_read: assert property(prop_deassert_bus_rd_after_read)
    // else
    // `uvm_error("system_bus_interface",$sformatf("Assertion deassert_bus_rd_after_read Failed: bus_rd not deasserted after data is put in bus"))

    //ASSERTION 12: shared and data_in_bus_lv1_lv2 should be only assserted after bus access has been granted
    property prop_assert_shared_and_data_in_bus_lv1_lv2;
        @(posedge clk)
            shared && data_in_bus_lv1_lv2 |-> bus_lv1_lv2_gnt_snoop;
    endproperty

    assert_shared_and_data_in_bus_lv1_lv2: assert property(prop_assert_shared_and_data_in_bus_lv1_lv2)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion assert_shared_and_data_in_bus_lv1_lv2 Failed: shared or data_in_bus_lv1_lv2 were high before bus access grant"))


    //ASSERTION 9 Repeated for remaining cores
    property gnt_proc_to_be_followed_by_req_proc_1;
        @(posedge clk)
            (bus_lv1_lv2_gnt_proc[1]) |-> $past(bus_lv1_lv2_req_proc[1]);
    endproperty
    gnt_proc_req_proc_label_1: assert property(gnt_proc_to_be_followed_by_req_proc)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_proc_to_be_followed_by_req_proc failed core 1: grant granted before request"))

    property gnt_proc_to_be_followed_by_req_proc_2;
        @(posedge clk)
            (bus_lv1_lv2_gnt_proc[2]) |-> $past(bus_lv1_lv2_req_proc[2]);
    endproperty
    gnt_proc_req_proc_label_2: assert property(gnt_proc_to_be_followed_by_req_proc)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_proc_to_be_followed_by_req_proc failed core 2: grant granted before request"))

    property gnt_proc_to_be_followed_by_req_proc_3;
        @(posedge clk)
            (bus_lv1_lv2_gnt_proc[3]) |-> $past(bus_lv1_lv2_req_proc[3]);
    endproperty
    gnt_proc_req_proc_label_3: assert property(gnt_proc_to_be_followed_by_req_proc)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_proc_to_be_followed_by_req_proc failedcore 3: grant granted before request"))


    //ASSERTION 10 Repeated for other cores

    property gnt_bus_to_be_followed_by_req_bus_1;
        @(posedge clk)
            (bus_lv1_lv2_gnt_snoop[1]) |-> $past(bus_lv1_lv2_req_snoop[1]);
    endproperty
    gnt_bus_req_bus_label_1: assert property(gnt_bus_to_be_followed_by_req_bus)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_bus_to_be_followed_by_req_bus failed core 1: grant granted before request"))

    property gnt_bus_to_be_followed_by_req_bus_2;
        @(posedge clk)
            (bus_lv1_lv2_gnt_snoop[2]) |-> $past(bus_lv1_lv2_req_snoop[2]);
    endproperty
    gnt_bus_req_bus_label_2: assert property(gnt_bus_to_be_followed_by_req_bus)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_bus_to_be_followed_by_req_bus failed core 2: grant granted before request"))

    property gnt_bus_to_be_followed_by_req_bus_3;
        @(posedge clk)
            (bus_lv1_lv2_gnt_snoop[3]) |-> $past(bus_lv1_lv2_req_snoop[3]);
    endproperty
    gnt_bus_req_bus_label_3: assert property(gnt_bus_to_be_followed_by_req_bus)
    else
    `uvm_error("system_bus_interface",$sformatf("Assertion gnt_bus_to_be_followed_by_req_bus failed core 3: grant granted before request"))

endinterface
