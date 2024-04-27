//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class four_writes_one_read extends base_test;

    //component macro
    `uvm_component_utils(four_writes_one_read)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", four_writes_one_read_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing four_writes_one_read test" , UVM_LOW)
    endtask: run_phase

endclass : four_writes_one_read

class four_writes_one_read_seq extends base_vseq; //bug 6 7
       //object macro
       `uvm_object_utils(four_writes_one_read_seq)
 
       cpu_transaction_c trans;
 
       //constructor
       function new (string name="four_writes_one_read_seq");
           super.new(name);
       endfunction : new
 
        virtual task body();
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[18:2]=='b11110000111000;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]=='b11110000111000;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]=='b11110000111000;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]=='b11110000111000;})
            // `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==14'b10111110000111000;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address[15:2]=='b11110000111000;})

        endtask
 
   endclass : four_writes_one_read_seq
 
