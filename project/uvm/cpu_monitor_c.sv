//=====================================================================
// Project: 4 core MESI cache design
// File Name: cpu_monitor_c.sv
// Description: cpu monitor component
// Designers: Venky & Suru
//=====================================================================

class cpu_monitor_c extends uvm_monitor;
    //component macro
    `uvm_component_utils(cpu_monitor_c)
    cpu_mon_packet_c packet;
    uvm_analysis_port #(cpu_mon_packet_c) mon_out;

    // Virtual interface of used to drive and observe CPU-LV1 interface signals
    virtual interface cpu_lv1_interface vi_cpu_lv1_if;

    covergroup cover_cpu_packet;
        option.per_instance = 1;
        option.name = "cover_cpu_packets";
        REQUEST: coverpoint packet.request_type;
        //Done: add coverpoints for Data, Address, etc.

        //CP for address type (Icache/Dcache)
        CACHE_TYPE: coverpoint packet.addr_type;

        // NUM_CYCLES: coverpoint packet.num_cycles;
        // {
        //     bins range[2] = {[1:5], [6:110]};
        // }

        //Data
        DATA: coverpoint packet.dat
        {
            option.auto_bin_max = 64;
        }
        
        //Addr 
        ADDR: coverpoint packet.address
        {
            option.auto_bin_max = 64;
        }   

        //Crosses
        X_REQUEST__CACHE_TYPE: cross REQUEST, CACHE_TYPE
        {
            illegal_bins NO_WRITE_ON_ICACHE = binsof (REQUEST) intersect {WRITE_REQ} && binsof (CACHE_TYPE) intersect {ICACHE};
        }

        X_DATA__CACHE_TYPE: cross DATA, CACHE_TYPE;
        X_REQUEST__DATA: cross REQUEST, DATA;
        X_REQUEST__ADDR: cross REQUEST, ADDR
        {
            //32'h4000_0000 = 32'd1073741824
            illegal_bins NO_WRITE_ON_ICACHE_ADDR = binsof (REQUEST) intersect {WRITE_REQ} && binsof (ADDR) intersect {[0:1073741824]};
        }

    endgroup


    //constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        mon_out = new ("mon_out", this);
        this.cover_cpu_packet = new();
    endfunction : new

    //UVM build phase ()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // throw error if virtual interface is not set
        if (!uvm_config_db#(virtual cpu_lv1_interface)::get(this, "","vif", vi_cpu_lv1_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vif"})
    endfunction: build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
        forever begin
            //Done: Code for the CPU monitor is incomplete
            //Add code to populate other fields of the cpu monitor packet
            //Ensure that your code can handle all possible cases (read, write
            //etc)
            @(posedge vi_cpu_lv1_if.cpu_rd or posedge vi_cpu_lv1_if.cpu_wr)
            packet = cpu_mon_packet_c::type_id::create("packet", this);

           // Adding address type
            if(vi_cpu_lv1_if.addr_bus_cpu_lv1 < 32'h4000_0000) begin
                packet.addr_type = ICACHE;
            end
            else begin
                packet.addr_type = DCACHE;
            end
            //TODO: make this increment every clock cycle
            @ (posedge vi_cpu_lv1_if.clk) begin
                packet.num_cycles++;
            end

            if(vi_cpu_lv1_if.cpu_rd === 1'b1) begin
                packet.request_type = READ_REQ;
            end

            //Adding Write request type and illegal bit
            else if (vi_cpu_lv1_if.cpu_wr === 1'b1) begin
                packet.request_type = WRITE_REQ;
                if(packet.addr_type == ICACHE) begin
                    packet.illegal = 1'b1;
                end
                else begin
                    packet.illegal = 1'b0;
                end
            end


//            if(vi_cpu_lv1_if.cpu_rd === 1'b1) begin
//                packet.request_type = READ_REQ;
//            end
            packet.address = vi_cpu_lv1_if.addr_bus_cpu_lv1;
            @(posedge vi_cpu_lv1_if.data_in_bus_cpu_lv1 or posedge vi_cpu_lv1_if.cpu_wr_done)
            packet.dat = vi_cpu_lv1_if.data_bus_cpu_lv1;
            @(negedge vi_cpu_lv1_if.cpu_rd or negedge vi_cpu_lv1_if.cpu_wr)
            mon_out.write(packet);
            cover_cpu_packet.sample();
        end
    endtask : run_phase

endclass : cpu_monitor_c
