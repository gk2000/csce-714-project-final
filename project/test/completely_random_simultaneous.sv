//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class completely_random_simultaneous extends base_test;

    //component macro
    `uvm_component_utils(completely_random_simultaneous)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", completely_random_simultaneous_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing completely_random_simultaneous test" , UVM_LOW)
    endtask: run_phase

endclass : completely_random_simultaneous

class completely_random_simultaneous_seq extends base_vseq;
       //object macro
       `uvm_object_utils(completely_random_simultaneous_seq)
 
       cpu_transaction_c trans1, trans2, trans3, trans4;
 
       //constructor
       function new (string name="completely_random_simultaneous_seq");
           super.new(name);
       endfunction : new
 
        virtual task body();
            repeat(100)
                fork
                    begin: CPU0
                        `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[0], {request_type == READ_REQ;})
                        `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; address>32'h4000_0000;})
                    end: CPU0
                    begin: CPU1
                        `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == READ_REQ;})
                        `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address>32'h4000_0000;})
                    end: CPU1
                    begin: CPU2
                        `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == READ_REQ;})
                        `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; address>32'h4000_0000;})
                    end: CPU2
                    begin: CPU3
                        `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[3], {request_type == READ_REQ;})
                        `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; address>32'h4000_0000;})
                    end: CPU3
                join

        endtask
 
   endclass : completely_random_simultaneous_seq
 
