//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class random_reads extends base_test;

    //component macro
    `uvm_component_utils(random_reads)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", random_reads_seq::type_id::get());
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", random_reads_ICACHE_seq::type_id::get());
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", random_reads_DCACHE_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing random_reads test" , UVM_LOW)
    endtask: run_phase

endclass : random_reads

class random_reads_seq extends base_vseq;
       //object macro
       `uvm_object_utils(random_reads_seq)
 
       cpu_transaction_c trans;
 
       //constructor
       function new (string name="random_reads_seq");
           super.new(name);
       endfunction : new
 
        virtual task body();
            repeat(500) begin
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ;})
            end
        endtask
 
endclass : random_reads_seq

class random_reads_ICACHE_seq extends base_vseq;
    //object macro
    `uvm_object_utils(random_reads_ICACHE_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="random_reads_ICACHE_seq");
        super.new(name);
    endfunction : new

     virtual task body();
         repeat(500) begin
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address<=32'h4000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address<=32'h4000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address<=32'h4000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address<=32'h4000_0000;})
         end
     endtask

endclass : random_reads_ICACHE_seq

class random_reads_DCACHE_seq extends base_vseq;
    //object macro
    `uvm_object_utils(random_reads_DCACHE_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="random_reads_DCACHE_seq");
        super.new(name);
    endfunction : new

     virtual task body();
         repeat(500) begin
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address>32'h4000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address>32'h4000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address>32'h4000_0000;})
         `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address>32'h4000_0000;})
         end
     endtask

endclass : random_reads_DCACHE_seq
 
