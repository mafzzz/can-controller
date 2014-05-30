// HVL Side for CAN

import xtlm_pkg::*; // For trans-language TLM channels.
`include "config.v"
//File Handlers
integer Rx_file;
integer Tx_file;

parameter debug=0;

	class scoreboard;

		xtlm_fifo #(bit[(data_width)-1:0]) monitorChannel;
		function new ();
		begin
			monitorChannel = new ("top.outputpipe");
			
			 Rx_file=$fopen("Rx_packet.txt","w");
			$fwrite(Rx_file,"RX_Packets\n");
			
		end
		endfunction

		task run();
			while (1)
			begin
				longint unsigned Rx_packet;
				monitorChannel.get(Rx_packet);
				$fwrite(Rx_file,"%0d\n",Rx_packet);
				
				if(debug)
				$display("Rx_packet=%d",Rx_packet);
			end
		endtask
    
	endclass

	

	class packet_gen ;

		xtlm_fifo #(bit[(data_width)-1:0]) driverChannel;
		longint Tx_packet=0;
		
    
		function new();			//Constructor 
			begin
				driverChannel = new ("top.inputpipe");		
				Tx_file=$fopen("Tx_packet.txt","w");
				$fwrite(Tx_file,"Tx_Packets\n");
				
			end
		endfunction

		task run;
		  input [31:0]runs;
		  
		repeat(runs)				
			begin			
				
				//Tx_packet=+1;
				if(randomize(Tx_packet) with {Tx_packet>0;Tx_packet<((2**63)-1);})	
				if(debug) $display("m=%d",Tx_packet);
			
			
			
						
					
				driverChannel.put(Tx_packet);
				$fwrite(Tx_file,"%0d\n",Tx_packet);
			end
		       	
       	driverChannel.flush_pipe;		
                 
		endtask

	endclass


	module can_hvl;

		scoreboard scb;
		packet_gen stim_gen;
		integer Packet_count;

		task packet_generate();
		  integer i;
			fork
			begin
				scb.run();
			end
			join_none
        
			fork			
			begin
				stim_gen.run(Packet_count);
			end			
			join_none
		endtask

		initial 
		fork
		  if($value$plusargs("PACKETS=%d",Packet_count))
		    $display("Generating %d Packets",Packet_count);
		    
		    		
			scb = new();
			stim_gen = new();
			packet_generate();
			
			
		join_none

	endmodule
 



