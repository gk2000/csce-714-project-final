//=====================================================================
// Project: 4 core MESI cache design
// File Name: system_bus_monitor_c.sv
// Description: system bus monitor component
// Designers: Venky & Suru
//=====================================================================

`include "sbus_packet_c.sv"

class system_bus_monitor_c extends uvm_monitor;
    //component macro
    `uvm_component_utils(system_bus_monitor_c)

    uvm_analysis_port #(sbus_packet_c) sbus_out;
    sbus_packet_c       s_packet;

    //Covergroup to monitor all the points within sbus_packet
    covergroup cover_sbus_packet;
        option.per_instance = 1;
        option.name = "cover_system_bus";
        REQUEST_TYPE: coverpoint  s_packet.bus_req_type;
        REQUEST_PROCESSOR: coverpoint s_packet.bus_req_proc_num;
        REQUEST_ADDRESS: coverpoint s_packet.req_address{
            option.auto_bin_max = 20;
        }
        READ_DATA: coverpoint s_packet.rd_data{
            option.auto_bin_max = 20;
        }
        //TODO: Add coverage for other fields of sbus_mon_packet

        BUS_REQ_SNOOP: coverpoint s_packet.bus_req_snoop
        {
            illegal_bins all_snoop = {4'b1111};
        }
    
        REQ_SERV_BY: coverpoint s_packet.req_serviced_by;

        WR_DATA_SNOOP: coverpoint s_packet.wr_data_snoop
        {
            option.auto_bin_max = 20;
        }   

        SNOOP_WR_REQ_FLAG: coverpoint s_packet.snoop_wr_req_flag;

        //to see if hit/miss
        CP_IN_CACHE: coverpoint s_packet.cp_in_cache;

        SHARED: coverpoint s_packet.shared;

        DIRTY_BLK_ADDR: coverpoint s_packet.proc_evict_dirty_blk_addr{
            option.auto_bin_max = 20;
        }

        DIRTY_BLK_DATA: coverpoint s_packet.proc_evict_dirty_blk_data{
            option.auto_bin_max = 20;
        }

        DIRTY_BLK_FLAG: coverpoint s_packet.proc_evict_dirty_blk_flag;

        //cross coverage
        //ensure each processor has read miss, write miss, invalidate, etc.
        X_PROC__REQ_TYPE: cross REQUEST_TYPE, REQUEST_PROCESSOR;
        X_PROC__ADDRESS: cross REQUEST_PROCESSOR, REQUEST_ADDRESS;
        X_PROC__DATA: cross REQUEST_PROCESSOR, READ_DATA;
        //TODO: Add relevant cross coverage (examples shown above)
        X_REQUEST_ADDRESS__REQ_TYPE: cross REQUEST_TYPE, REQUEST_ADDRESS{
            ignore_bins NO_REQ_TO_ICACHE= binsof(REQUEST_TYPE) && binsof(REQUEST_ADDRESS) intersect {[0:1073741824]};
        }
        X_REQUEST_ADDRESS__SNOOP_WR_REQ_FLAG: cross REQUEST_ADDRESS, SNOOP_WR_REQ_FLAG{
            ignore_bins NO_SNOOP_TO_ICACHE= binsof(SNOOP_WR_REQ_FLAG) && binsof(REQUEST_ADDRESS) intersect {[0:1073741824]};
        }
        X_PROC__CP_IN_CACHE: cross REQUEST_PROCESSOR, CP_IN_CACHE;
        X_PROC__SHARED: cross REQUEST_PROCESSOR, SHARED;
        X_PROC__DIRTY_BLK_FLAG: cross REQUEST_PROCESSOR, DIRTY_BLK_FLAG;

        X_PROC__DIRTY_BLK_ADDR: cross REQUEST_PROCESSOR, DIRTY_BLK_ADDR{
            ignore_bins NO_DIRTY_BLK_ADDR_IN_ICACHE= binsof(REQUEST_PROCESSOR) && binsof(DIRTY_BLK_ADDR) intersect {[0:1073741824]};
        }
        X_PROC__DIRTY_BLK_DATA: cross REQUEST_PROCESSOR, DIRTY_BLK_DATA;
        X_PROC__WR_DATA_SNOOP: cross REQUEST_PROCESSOR, WR_DATA_SNOOP;
        X_PROC__SNOOP_REQ_FLAG: cross REQUEST_PROCESSOR, SNOOP_WR_REQ_FLAG;
        X_PROC__REQ_SERV_BY: cross REQUEST_PROCESSOR, REQ_SERV_BY;
        X_PROC__BUS_REQ_SNOOP: cross REQUEST_PROCESSOR, BUS_REQ_SNOOP;
   


    endgroup

    // Virtual interface of used to observe system bus interface signals
    virtual interface system_bus_interface vi_sbus_if;

    //constructor
    function new (string name, uvm_component parent);
        super.new(name, parent);
        sbus_out = new("sbus_out", this);
        this.cover_sbus_packet = new();
    endfunction : new

    //UVM build phase ()
    function void build_phase(uvm_phase phase);
        super.build_phase(phase);
        // throw error if virtual interface is not set
        if (!uvm_config_db#(virtual system_bus_interface)::get(this, "","v_sbus_if", vi_sbus_if))
            `uvm_fatal("NO_VIF",{"virtual interface must be set for: ",get_full_name(),".vi_sbus_if"})
    endfunction: build_phase

    //UVM run phase()
    task run_phase(uvm_phase phase);
        `uvm_info(get_type_name(), "RUN Phase", UVM_LOW)
        forever begin
        //TODO: Code for the system bus monitor is minimal!
        //Add code to observe other cases
        //Add code for dirty block eviction
        //Snoop requests, service time, etc
            // trigger point for creating the packet
            @(posedge (|vi_sbus_if.bus_lv1_lv2_gnt_proc));
            `uvm_info(get_type_name(), "Packet creation triggered", UVM_LOW)
            s_packet = sbus_packet_c::type_id::create("s_packet", this);


            fork 
                begin: lv2_write_check
                    @(posedge vi_sbus_if.lv2_wr && !vi_sbus_if.cp_in_cache)
                    s_packet.proc_evict_dirty_blk_flag = 1;
                    s_packet.proc_evict_dirty_blk_data = vi_sbus_if.data_bus_lv1_lv2;
                    s_packet.proc_evict_dirty_blk_addr = vi_sbus_if.addr_bus_lv1_lv2;
                end: lv2_write_check
            join_none

            // wait for assertion of either bus_rd, bus_rdx or invalidate before monitoring other bus activities
            // lv2_rd for I-cache cases
            @(posedge(vi_sbus_if.bus_rd | vi_sbus_if.bus_rdx | vi_sbus_if.invalidate | vi_sbus_if.lv2_rd));
            fork
                begin: cp_in_cache_check
                    // check for cp_in_cache assertion
                    @(posedge vi_sbus_if.cp_in_cache) s_packet.cp_in_cache = 1;
                end : cp_in_cache_check
                begin: shared_check
                    // check for shared signal assertion when data_in_bus_lv1_lv2 is also high
                    wait(vi_sbus_if.shared & vi_sbus_if.data_in_bus_lv1_lv2) s_packet.shared = 1;
                end : shared_check

                begin: bus_req_snoop_check
                    @(posedge vi_sbus_if.cp_in_cache);
                    s_packet.bus_req_snoop = vi_sbus_if.bus_lv1_lv2_req_snoop;
                end: bus_req_snoop_check

                begin: snoop_lv2_write_check
                    wait(vi_sbus_if.cp_in_cache & vi_sbus_if.lv2_wr)
                    s_packet.wr_data_snoop = vi_sbus_if.data_bus_lv1_lv2;
                    s_packet.snoop_wr_req_flag = 1'b1;
                end: snoop_lv2_write_check
            join_none
            

            // bus request type
            if (vi_sbus_if.bus_rd === 1'b1)
                s_packet.bus_req_type = BUS_RD;
            else if (vi_sbus_if.bus_rdx === 1'b1)
                s_packet.bus_req_type = BUS_RDX;
            else if (vi_sbus_if.invalidate === 1'b1)
                s_packet.bus_req_type = INVALIDATE;
            else if (vi_sbus_if.bus_rd === 1'b1 && vi_sbus_if.addr_bus_lv1_lv2<32'h4000_0000)
                s_packet.bus_req_type = ICACHE_RD;

            // proc which requested the bus access
            case (1'b1)
                vi_sbus_if.bus_lv1_lv2_gnt_proc[0]: s_packet.bus_req_proc_num = REQ_PROC0;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[1]: s_packet.bus_req_proc_num = REQ_PROC1;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[2]: s_packet.bus_req_proc_num = REQ_PROC2;
                vi_sbus_if.bus_lv1_lv2_gnt_proc[3]: s_packet.bus_req_proc_num = REQ_PROC3;
            endcase

            // address requested
            s_packet.req_address = vi_sbus_if.addr_bus_lv1_lv2;

            // fork and call tasks
            fork: update_info
                begin
                    @(|vi_sbus_if.bus_lv1_lv2_req_snoop)// check if any of the cpu is requesting a snoop 
                    s_packet.bus_req_snoop = vi_sbus_if.bus_lv1_lv2_req_snoop;
                end
                begin
                    @(vi_sbus_if.cp_in_cache)
                    wait(vi_sbus_if.lv2_wr_done)
                    s_packet.snoop_wr_req_flag = 1'b1;
                    s_packet.wr_data_snoop = vi_sbus_if.data_bus_lv1_lv2;
                end
                // to determine which of snoops or L2 serviced read miss
                begin: req_service_check
                    if (s_packet.bus_req_type == BUS_RD | s_packet.bus_req_type == BUS_RDX)
                    begin
                        @(posedge vi_sbus_if.data_in_bus_lv1_lv2);
                        `uvm_info(get_type_name(), "Bus read or bus readX successful", UVM_LOW)
                        s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
                        // check which had grant asserted
                        case (1'b1)
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
                            vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
                            vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
                        endcase
                    end
                end: req_service_check
                begin: ICACHE_req_service_check
                    if(s_packet.bus_req_type == ICACHE_RD)
                    begin
                        @(posedge vi_sbus_if.data_in_bus_lv1_lv2);
                        `uvm_info(get_type_name(), "ICACHE_RD successful", UVM_LOW)
						s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
						// check which had grant asserted
						case (1'b1)
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
						vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
						endcase
					end
				end: ICACHE_req_service_check

                begin: invalidate_service_check
                    if(s_packet.bus_req_type == INVALIDATE)
                    begin
                        @(posedge vi_sbus_if.all_invalidation_done);
                        `uvm_info(get_type_name(), "INVALIDATION successful", UVM_LOW)
                    end
                end : invalidate_service_check

                begin: read_x_check
                    if(s_packet.bus_req_type == BUS_RDX)
                    begin
                        @(posedge vi_sbus_if.data_in_bus_lv1_lv2);
                        `uvm_info(get_type_name(), "BUS_RDX successful", UVM_LOW)
                        s_packet.rd_data = vi_sbus_if.data_bus_lv1_lv2;
                        // check which had grant asserted
						case (1'b1)
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[0]: s_packet.req_serviced_by = SERV_SNOOP0;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[1]: s_packet.req_serviced_by = SERV_SNOOP1;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[2]: s_packet.req_serviced_by = SERV_SNOOP2;
						vi_sbus_if.bus_lv1_lv2_gnt_snoop[3]: s_packet.req_serviced_by = SERV_SNOOP3;
						vi_sbus_if.bus_lv1_lv2_gnt_lv2     : s_packet.req_serviced_by = SERV_L2;
						endcase
					end
                end : read_x_check

            join_none : update_info

            // wait until request is processed and send data
            @(negedge vi_sbus_if.bus_lv1_lv2_req_proc[0] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[1] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[2] or negedge vi_sbus_if.bus_lv1_lv2_req_proc[3]);

            `uvm_info(get_type_name(), "Packet to be written", UVM_LOW)

            // disable all spawned child processes from fork
            disable fork;

            // write into scoreboard after population of the packet fields
            sbus_out.write(s_packet);
            cover_sbus_packet.sample();
        end
    endtask : run_phase

endclass : system_bus_monitor_c
