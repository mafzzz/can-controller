//
//
//DESCRIPTION: HVL Side for CAN
//Code re-used from Sameer's booth model
//
//

`include "def.pkg"
import xtlm_pkg::*; // For trans-language TLM channels.

import definitions::*;
`define DATA_PACKET	Tx_packet[0]		//Randomization macro for detecting Data or Req packet
`define ERROR_FLAG	Tx_packet[5]		//Randomization macro for Error detection
`define DEBUG
//File Handlers
integer Rx_file;
integer Tx_file;
integer ID_file;

`ifdef DEBUG
longint unsigned Tx_queue[$];
longint unsigned Rx_queue[$];		//Internal queues used for debug
`endif

//Scoreboard for Received packets from XRTL transactor
	class scoreboard;

		xtlm_fifo #(bit[(DATA_SIZE)-1:0]) monitorChannel;
		bit [DATA_SIZE-1:0] Rx_packet;
		function new ();				//Constructor
		begin
			monitorChannel = new ("top.outputpipe");
			 Rx_file=$fopen("Rx_packet.txt","w");
			$fwrite(Rx_file,"RX_Packets\n");
			
		end
		endfunction

		task run();
			while (1)
			begin
				monitorChannel.get(Rx_packet);			//As long as FIFO has data
				$fwrite(Rx_file,"%0d\n",Rx_packet);			//Write data packets to file 
				`ifdef DEBUG
				Rx_queue.push_front(Rx_packet);
				`endif
			end
		endtask
    
	endclass

	//Randomized class to generate ID's for CAN nodes
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
				
				//Each node requires 11 bit ID i.e almost 2 bytes(as FIFO transmits in bytes)
				if(randomize(ID) with {ID>0;ID<((2**(Total_Nodes*16))-1);})	
				ID_driverChannel.put(ID);
				$fwrite(ID_file,"%0d\n",ID);
			end
		       	
		ID_driverChannel.flush_pipe;		
                 
		endtask

	endclass
	
	//Randomize class for generating Tx Packets to be sent to XRTL Transactor
	
	class Data_Randomize;
	rand bit[DATA_SIZE-1:0] Tx_packet;
	
	int DataFrame_wt=90,ReqFrame_wt=10,ErrorOn_wt=20,ErrorOff_wt=80; 
	
	constraint Data_frame {
	`DATA_PACKET dist {1:=DataFrame_wt,0:=ReqFrame_wt};		//Weighted Randomization for generating Data , Req Frames
	`ERROR_FLAG dist {1:=ErrorOn_wt,0:=ErrorOff_wt};				// & Error injection
	}
	
	endclass
	
	//Tx packet generator class
	class packet_gen ;

		xtlm_fifo #(bit[(DATA_SIZE)-1:0]) Data_driverChannel;
		Data_Randomize RandTx_Data;					//Handle to Data_Randomize class
		
    
		function new();			//Constructor 
			begin
				Data_driverChannel = new ("top.inputpipe_data");		
				Tx_file=$fopen("Tx_packet.txt","w");
				$fwrite(Tx_file,"Tx_Packets\n");
				RandTx_Data=new();
				
			end
		endfunction

		task run;
		  input [31:0]runs;			//Runs specified from Command line
		  
		repeat(runs)				
			begin			
				
				
				RandTx_Data.constraint_mode(0);
				RandTx_Data.Data_frame.constraint_mode(1);		//Enable required constraints,if additional constraints included in future
				assert(RandTx_Data.randomize());					//assert randomization
				Data_driverChannel.put(RandTx_Data.Tx_packet);
				$fwrite(Tx_file,"%0d\n",RandTx_Data.Tx_packet);		//Drive Tx packet onto SCEMI pipe
				`ifdef DEBUG
				Tx_queue.push_front(RandTx_Data.Tx_packet);
				`endif
			end
		       	
       	Data_driverChannel.flush_pipe;		
                 
		endtask

	endclass

	
	//HVL module

	module can_hvl;

		scoreboard scb;			//Handle declarations
		packet_gen stim_gen;
		ID_gen	Id_gen;
		integer Packet_count;	//internal counts for scoreboard
		int unsigned Data_PacketCount,Req_PacketCount,Lost_PacketCount;
		longint unsigned tq[$];

		task packet_generate();			//Parallel tasks to monitor & generate data/ID's
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
		  if($value$plusargs("PACKETS=%d",Packet_count))			//No. of packets to be specified via command line
		    $display("Generating %d Packets",Packet_count);
		    
		    		
			scb = new();
			stim_gen = new();
			Id_gen=new();
			packet_generate();
			
			
		join_none
	
	
	//Final block for HVL Scoreboard 
	final
	begin
	foreach(Tx_queue[i])
	begin
		if(Tx_queue[i][0]==1) Data_PacketCount+=1;
		else				   Req_PacketCount+=1;		
	end	
	foreach(Tx_queue[i])
		begin
			if(Tx_queue[i][0])				//Lost packet check i.e. whether all data packets generated were received back from HDL
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
	$display( "------------------------------------------PACKET COUNTS------------------------------------------------");
	$display("No.of Packets Received:			%d",Rx_queue.size());
	$display("No.Of Lost Packets:		       		 %d",Lost_PacketCount);
	`ifdef DEBUG
	$display("HVL Output Queue:%p",Rx_queue.size());
	`endif
	end
	endmodule
 



