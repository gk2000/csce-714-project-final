//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class all_cores_read_snoop extends base_test;

    //component macro
    `uvm_component_utils(all_cores_read_snoop)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", all_cores_read_snoop_seq::type_id::get());
        super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing multiple_write_same_block test" , UVM_LOW)
    endtask: run_phase

endclass : all_cores_read_snoop

class all_cores_read_snoop_seq extends base_vseq;
       //object macro
       `uvm_object_utils(all_cores_read_snoop_seq)

       cpu_transaction_c trans;
       parameter ADDR_WID_LV1        = `ADDR_WID_LV1       ;
       rand logic [ADDR_WID_LV1-1:0] rand_address;
 
       //constructor
       function new (string name="all_cores_read_snoop_seq");
           super.new(name);
       endfunction : new
 
        virtual task body();
            repeat(5) begin
                randomize(rand_address);
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address==rand_address;})
            end

            repeat(5) begin
                randomize(rand_address);
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address==rand_address;})
            end

            repeat(5) begin
                randomize(rand_address);
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address==rand_address;})
            end

            repeat(5) begin
                randomize(rand_address);
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address==rand_address;})
                `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address==rand_address;})
            end

        endtask
 
   endclass : all_cores_read_snoop_seq
