//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class simultaneous_write extends base_test;

    //component macro
    `uvm_component_utils(simultaneous_write)
    virtual_sequencer_c vsequencer2;

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        // vsequencer2 = virtual_sequencer_c::type_id::create("vsequencer2", this);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", simultaneous_write_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing simultaneous_write test" , UVM_LOW)
    endtask: run_phase

endclass : simultaneous_write

class simultaneous_write_seq extends base_vseq;
       //object macro
       `uvm_object_utils(simultaneous_write_seq)
 
       cpu_transaction_c trans1, trans2, trans3, trans4;
 
       //constructor
       function new (string name="simultaneous_write_seq");
           super.new(name);
       endfunction : new
 
        virtual task body();

            fork
                begin: CPU0
                    `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address[15:2]==14'b00111110000111;})
                    
                end: CPU0
                begin: CPU1
                    `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==14'b00111110000111;})
                end: CPU1
                begin: CPU2
                    `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address[15:2]==14'b00111110000111;})
                end: CPU2
                begin: CPU3
                    `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==14'b00111110000111;})
                end: CPU3
            join

        endtask
 
   endclass : simultaneous_write_seq
 
