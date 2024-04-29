//=====================================================================
// Project: 4 core MESI cache design
// File Name: write_read.sv
// Description: Test for read-miss to I-cache
// Designers: Venky & Suru
//=====================================================================

class invalidate extends base_test;

    //component macro
    `uvm_component_utils(invalidate)

    //Constructor
    function new(string name, uvm_component parent);
        super.new(name, parent);
    endfunction : new

    //UVM build phase
    function void build_phase(uvm_phase phase);
        uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", invalidate_seq::type_id::get());
    //     uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", invalidate_2_seq::type_id::get());
	// uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", invalidate_3_seq::type_id::get());
	// uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", invalidate_4_seq::type_id::get());
	// uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", invalidate_5_seq::type_id::get());
	// uvm_config_wrapper::set(this, "tb.vsequencer.run_phase", "default_sequence", invalidate_6_seq::type_id::get());
	super.build_phase(phase);
    endfunction : build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "Executing invalidate test" , UVM_LOW)
    endtask: run_phase

endclass : random_write_read
 

class invalidate_seq extends base_vseq;
      //object macro
      `uvm_object_utils(invalidate_seq)
      cpu_transaction_c trans;
      //constructor
      function new (string name="invalidate_seq");
          super.new(name);
      endfunction : new
      
      virtual task body();
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h5000_0000;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == 32'h5000_0000;})
	    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; address == 32'h5000_0000;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == 32'h5000_0040;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h5000_0040;})
	    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address == 32'h5000_0040;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == 32'h5000_0060;})
	    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == 32'h5000_0060;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; address == 32'h5000_0060;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == 32'h5000_0080;})
            `uvm_do_on_with(trans, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == 32'h5000_0080;})
	    `uvm_do_on_with(trans, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; address == 32'h5000_0080;})
        
    endtask
  
 endclass : invalidate_seq

  class invalidate_2_seq extends base_vseq;
        //object macro
        `uvm_object_utils(invalidate_2_seq)
  
        cpu_transaction_c trans1;
        rand logic[31:0] rand_addr;
        //constructor
        function new (string name="invalidate_2_seq");
            super.new(name);
        endfunction : new
  
        virtual task body();
          repeat(500) begin
              randomize(rand_addr);
              while(rand_addr<32'h4000_0000) begin
                  randomize(rand_addr);
              end
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; address ==rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address ==rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[2], {request_type == WRITE_REQ; address ==rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
            `uvm_do_on_with(trans1, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; address ==rand_addr;})
  
	end
      endtask
endclass : invalidate_2_seq

   class invalidate_3_seq extends base_vseq;
         //object macro
         `uvm_object_utils(invalidate_3_seq)
 
         cpu_transaction_c trans2;
         rand logic[31:0] rand_addr;
         //constructor
         function new (string name="invalidate_3_seq");
             super.new(name);
         endfunction : new
 
         virtual task body();
           repeat(500) begin
               randomize(rand_addr);
               while(rand_addr<32'h4000_0000) begin
                   randomize(rand_addr);
               end
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[0], {request_type == WRITE_REQ; address ==rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == WRITE_REQ; address ==rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; address ==rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})
             `uvm_do_on_with(trans2, p_sequencer.cpu_seqr[3], {request_type == WRITE_REQ; address ==rand_addr;})
 
         end
       endtask

  
    endclass : invalidate_3_seq

   class invalidate_4_seq extends base_vseq;
          //object macro
          `uvm_object_utils(invalidate_4_seq)
  
          cpu_transaction_c trans3;
          rand logic[31:0] rand_req_type;
          //constructor
          function new (string name="invalidate_4_seq");
              super.new(name);
          endfunction : new
  
          virtual task body();
            repeat(500) begin
//                randomize(rand_addr);
		randomize(rand_req_type);
//                while(rand_addr<=32'h4000_0000) begin
//                    randomize(rand_addr);
//                end
              `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[0], {request_type == rand_req_type; address == 32'h5000_0000;})
              `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[0], {request_type == rand_req_type; address == 32'h5001_0000;})
              `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[0], {request_type == rand_req_type; address == 32'h5002_0000;})
              `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[0], {request_type == rand_req_type; address == 32'h5003_0000;})
              `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[0], {request_type == rand_req_type; address == 32'h5004_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[1], {request_type == rand_req_type; address == 32'h5005_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[1], {request_type == rand_req_type; address == 32'h5006_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[1], {request_type == rand_req_type; address == 32'h5007_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[1], {request_type == rand_req_type; address == 32'h5008_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[1], {request_type == rand_req_type; address == 32'h5009_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == rand_req_type; address == 32'h500A_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == rand_req_type; address == 32'h500B_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == rand_req_type; address == 32'h500C_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == rand_req_type; address == 32'h500D_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[2], {request_type == rand_req_type; address == 32'h500E_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[3], {request_type == rand_req_type; address == 32'h500F_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[3], {request_type == rand_req_type; address == 32'h5010_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[3], {request_type == rand_req_type; address == 32'h5020_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[3], {request_type == rand_req_type; address == 32'h5030_0000;})
               `uvm_do_on_with(trans3, p_sequencer.cpu_seqr[3], {request_type == rand_req_type; address == 32'h5040_0000;})
              
 
          end
        endtask
  endclass : invalidate_4_seq

    class invalidate_5_seq extends base_vseq;
           //object macro
           `uvm_object_utils(invalidate_5_seq)
 
           cpu_transaction_c trans4;
//           rand logic[31:0] rand_req_type;
           //constructor
           function new (string name="invalidate_5_seq");
               super.new(name);
           endfunction : new
 
           virtual task body();
//             repeat(500) begin
 //                randomize(rand_addr);
//                 randomize(rand_req_type);
 //                while(rand_addr<=32'h4000_0000) begin
 //                    randomize(rand_addr);
 //                end
               `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h3000_0000;})
               `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h3001_0000;})
               `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h3002_0000;})
               `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h3003_0000;})
               `uvm_do_on_with(trans4, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == 32'h3004_0000;})
 //          end
         endtask
   endclass : invalidate_5_seq

     class invalidate_6_seq extends base_vseq;
            //object macro
            `uvm_object_utils(invalidate_6_seq)
 
            cpu_transaction_c trans5;
            rand logic[31:0] rand_addr;
            //constructor
            function new (string name="invalidate_6_seq");
                super.new(name);
            endfunction : new
 
            virtual task body();
              repeat(500) begin
                  randomize(rand_addr);
 //                 randomize(rand_req_type);
                  while(rand_addr>32'h4000_0000) begin
                      randomize(rand_addr);
                  end
                `uvm_do_on_with(trans5, p_sequencer.cpu_seqr[0], {request_type == READ_REQ; address == rand_addr;})
                `uvm_do_on_with(trans5, p_sequencer.cpu_seqr[1], {request_type == READ_REQ; address == rand_addr;})
                `uvm_do_on_with(trans5, p_sequencer.cpu_seqr[2], {request_type == READ_REQ; address == rand_addr;})
                `uvm_do_on_with(trans5, p_sequencer.cpu_seqr[3], {request_type == READ_REQ; address == rand_addr;})

            end
          endtask
    endclass : invalidate_6_seq
 

