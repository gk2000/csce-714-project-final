//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class multiple_random_write_same_block extends base_test;

    //component macro
    `uvm_component_utils(multiple_random_write_same_block)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", multiple_random_write_same_block_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing multiple_random_write_same_block test" , UVM_LOW)
    endtask: run_phase

endclass : multiple_random_write_same_block

class multiple_random_write_same_block_seq extends base_vseq;
       //object macro
       `uvm_object_utils(multiple_random_write_same_block_seq)
 
       cpu_transaction_c trans;
       rand logic[13:0] rand_tag;
 
       //constructor
       function new (string name="multiple_random_write_same_block_seq");
           super.new(name);
       endfunction : new
 
        virtual task body();
            repeat(500) begin
                randomize(rand_tag);
                repeat(5) begin
                    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==rand_tag;})
                    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==rand_tag;})
                    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==rand_tag;})
                    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address[15:2]==rand_tag;})
                end
            end
        endtask
 
   endclass : multiple_random_write_same_block_seq
 
