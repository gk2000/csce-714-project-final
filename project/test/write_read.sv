//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class write_read extends base_test;

    //component macro
    `uvm_component_utils(write_read)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_read_2_seq::type_id::get());
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_read_1_seq::type_id::get());
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_read_3_seq::type_id::get());
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", write_read_4_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing write_read test" , UVM_LOW)
    endtask: run_phase

endclass : write_read
 

class write_read_1_seq extends base_vseq; //bug 3
      //object macro
      `uvm_object_utils(write_read_1_seq)
      
      cpu_transaction_c trans;
      
      //constructor
      function new (string name="write_read_1_seq");
          super.new(name);
      endfunction : new
      
      virtual task body();
          `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359;})
          `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359;})
          `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359; data == 32'hEEDD_CCAA;})
        //   `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359; data == 32'hBBCC_DDEE;}) 
          endtask
  
  endclass : write_read_1_seq


  class write_read_2_seq extends base_vseq; //bug 1
    //object macro
    `uvm_object_utils(write_read_2_seq)
    
    cpu_transaction_c trans;
    
    //constructor
    function new (string name="write_read_2_seq");
        super.new(name);
    endfunction : new
    
    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359; data == 32'hEEDD_CCAB;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359; data == 32'hEEDD_CCAD;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359; data == 32'hEEDD_CCAA;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359; data == 32'hBBCC_DDEE;}) 
        endtask

endclass : write_read_2_seq

class write_read_3_seq extends base_vseq; //bug2
    //object macro
    `uvm_object_utils(write_read_3_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="write_read_3_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4359;})
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4358; data == 32'hBBCC_DDEE;})
    endtask

endclass: write_read_3_seq

class write_read_4_seq extends base_vseq; //bug9
    //object macro
    `uvm_object_utils(write_read_4_seq)

    cpu_transaction_c trans;

    //constructor
    function new (string name="write_read_4_seq");
        super.new(name);
    endfunction : new

    virtual task body();
        `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; access_cache_type == DCACHE_ACC; address == 32'h5000_4358; data == 32'hBBCC_DDEE;})
    endtask

endclass: write_read_4_seq