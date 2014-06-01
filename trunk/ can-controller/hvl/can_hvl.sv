// HVL Side for CAN

import xtlm_pkg::*; // For trans-language TLM channels.
//`include "def.pkg"
import definitions::*;
`define DATA_PACKET	Tx_packet[0]
`define ERROR_FLAG	Tx_packet[5]
`define DEBUG
//File Handlers
integer Rx_file;
integer Tx_file;
integer ID_file;

longint unsigned Tx_queue[$];
longint unsigned Rx_queue[$];


	class scoreboard;

		xtlm_fifo #(bit[(DATA_SIZE)-1:0]) monitorChannel;
		bit [DATA_SIZE-1:0] Rx_packet;
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
				monitorChannel.get(Rx_packet);
				$fwrite(Rx_file,"%0d\n",Rx_packet);
				`ifdef DEBUG
				Rx_queue.push_front(Rx_packet);
				`endif
			end
		endtask
    
	endclass

		class ID_gen ;

		xtlm_fifo #(bit[(Total_Nodes*16)-1:0]) ID_driverChannel;
		bit [(Total_Nodes*16)-1:0] ID=0;
		
    
		function new();			//Constructor 
			begin
				ID_driverChannel = new ("top.inputpipe_id");		
				ID_file=$fopen("ID_gen.txt","w");
				$fwrite(ID_file,"ID_Generated\n");
			end
		endfunction

		task run;
		  input [31:0]runs;
		  
		repeat(runs)				
			begin			
				
				
				if(randomize(ID) with {ID>0;ID<((2**(Total_Nodes*16))-1);})	
				ID_driverChannel.put(ID);
				$fwrite(ID_file,"%0d\n",ID);
			end
		       	
		ID_driverChannel.flush_pipe;		
                 
		endtask

	endclass
	
	class Data_Randomize;
	rand bit[DATA_SIZE-1:0] Tx_packet;
	int DataFrame_wt=90,ReqFrame_wt=10,ErrorOn_wt=20,ErrorOff_wt=80; 
	constraint Data_frame {
	`DATA_PACKET dist {1:=DataFrame_wt,0:=ReqFrame_wt};
	`ERROR_FLAG dist {1:=ErrorOn_wt,0:=ErrorOff_wt};
	}
	
	endclass
	
	class packet_gen ;

		xtlm_fifo #(bit[(DATA_SIZE)-1:0]) Data_driverChannel;
		Data_Randomize RandTx_Data;
		
    
		function new();			//Constructor 
			begin
				Data_driverChannel = new ("top.inputpipe_data");		
				Tx_file=$fopen("Tx_packet.txt","w");
				$fwrite(Tx_file,"Tx_Packets\n");
				RandTx_Data=new();
				
			end
		endfunction

		task run;
		  input [31:0]runs;
		  
		repeat(runs)				
			begin			
				
				
				RandTx_Data.constraint_mode(0);
				RandTx_Data.Data_frame.constraint_mode(1);
				assert(RandTx_Data.randomize());
				Data_driverChannel.put(RandTx_Data.Tx_packet);
				$fwrite(Tx_file,"%0d\n",RandTx_Data.Tx_packet);
				`ifdef DEBUG
				Tx_queue.push_front(RandTx_Data.Tx_packet);
				`endif
			end
		       	
       	Data_driverChannel.flush_pipe;		
                 
		endtask

	endclass


	module can_hvl;

		scoreboard scb;
		packet_gen stim_gen;
		ID_gen	Id_gen;
		integer Packet_count;
		int unsigned Data_PacketCount,Req_PacketCount,Lost_PacketCount;
		longint unsigned tq[$];

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
			
			fork			
			begin
				Id_gen.run(1);
			end			
			join_none
		endtask

		initial 
		fork
		  if($value$plusargs("PACKETS=%d",Packet_count))
		    $display("Generating %d Packets",Packet_count);
		    
		    		
			scb = new();
			stim_gen = new();
			Id_gen=new();
			packet_generate();
			
			
		join_none
		
	final
	begin
	foreach(Tx_queue[i])
	begin
		if(Tx_queue[i][0]==1) Data_PacketCount+=1;
		else				   Req_PacketCount+=1;
	end	
	foreach(Tx_queue[i])
		begin
			if(Tx_queue[i][0])
			begin
			tq=Rx_queue.find_first with (item==Tx_queue[i]);
			if(!tq.size()) Lost_PacketCount+=1;
			end
		end
	$display( "-------------------------------------------------------------------------------------------------------");
	$display( "----------------------------------------STIMULUS SCOREBOARD--------------------------------------------");
	$display("No.Of Packets generated:			%d",Packet_count);
	$display("No.Of Data Packets:				 %d",Data_PacketCount);
	$display("No.Of Req Packets:				 %d",Req_PacketCount);
	$display( "-------------------------------------------------------------------------------------------------------");
	$display( "----------------------------------------PACKET COUNTS--------------------------------------------------");
	$display("No.of Packets Revieved:			%d",Rx_queue.size());
	$display("No.Of Lost Packets:		       		 %d",Lost_PacketCount);
	`ifdef DEBUG
	$display("HVL Output Queue:%p",Rx_queue.size());
	`endif
	end
	endmodule
 



