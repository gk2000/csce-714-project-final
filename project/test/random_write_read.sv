//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class random_write_read extends base_test;

    //component macro
    `uvm_component_utils(random_write_read)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", random_write_read_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing random_write_read test" , UVM_LOW)
    endtask: run_phase

endclass : random_write_read
 

class random_write_read_seq extends base_vseq;
      //object macro
      `uvm_object_utils(random_write_read_seq)
      
      cpu_transaction_c trans;
      rand logic[31:0] rand_addr;
      //constructor
      function new (string name="random_write_read_seq");
          super.new(name);
      endfunction : new
      
      virtual task body();
        repeat(500) begin
            randomize(rand_addr);
            while(rand_addr<=32'h4000_0000) begin
                randomize(rand_addr);
            end
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; address == rand_addr;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})
        end
    endtask
  
  endclass : random_write_read_seq


