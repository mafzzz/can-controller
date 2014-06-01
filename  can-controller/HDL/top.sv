//This is a top level testbench. HDL side. Contains XRTL Transactor



	`include "def.pkg"

	module top;

	bit clock;
	bit reset;
	
	logic [Total_Nodes-1:0] data_in_req,data_out_req,data,Retransmit;
	bit [DATA_SIZE-1:0] In_packet[0:Total_Nodes-1],Rx_packet[0:Total_Nodes-1];
	bit [ID_SIZE-1:0] ID[0:Total_Nodes-1],Tx_ID[0:Total_Nodes-1], Rx_ID[0:Total_Nodes-1];
	
	`ifndef VELOCE
	longint	unsigned Input_queue[$];
	longint	unsigned Output_queue[$];
	longint unsigned Lost_PacketCount;
	int	count[int]='{default:0};
	longint unsigned tq[$];
	`endif
	
	`ifdef ASSERT_EN
	logic [Total_Nodes-1:0] SLAVE_ACK,bitchk_en;
	wire ACK=|SLAVE_ACK;
	wire BIT_CHK=|bitchk_en;
	`endif
	
	
	clock_gen cg1(.clock);
	
	can_bus bus (data);

		can		c0(.*,.In_packet(In_packet[0]),.Rx_packet(Rx_packet[0]),.Tx_ID(Tx_ID[0]),.Rx_ID(Rx_ID[0]),
	                  .data_in_req(data_in_req[0]),.data_out_req(data_out_req[0]),.data(data[0]),
	                   .Retransmit(Retransmit[0])
	                   `ifdef ASSERT_EN
	                   ,.bitchk_en(bitchk_en[0]),.SLAVE_ACK(SLAVE_ACK[0])
	                   `endif);
					   
	genvar i;
	generate
	for(i=1;i<=Total_Nodes-1;i++)
	begin
	can		c (.*,.In_packet(In_packet[i]),.Rx_packet(Rx_packet[i]),.Tx_ID(Tx_ID[i]),.Rx_ID(Rx_ID[i]),
	         .data_in_req(data_in_req[i]),.data_out_req(data_out_req[i]),.data(data[i]),.Retransmit(Retransmit[i])
	          `ifdef ASSERT_EN
	           ,.bitchk_en(bitchk_en[i]),.SLAVE_ACK(SLAVE_ACK[i])
	            `endif);
	end
	endgenerate


	


	initial
	begin
	reset=1'b1;
	repeat(2)  @(negedge clock); reset=~reset;
	end
	
	`ifndef VELOCE
	always_comb
	count[c0.state]=count[c0.state]+1;
	
	
	final
	begin
		foreach(Input_queue[i])
		begin
			if(Input_queue[i][0])
			begin
			tq=Output_queue.find_first with (item==Input_queue[i]);
			if(!tq.size()) Lost_PacketCount+=1;
			end
		end
		$display("-----------------------------------------------");
		$display("------------BUS TRANSACTION SCOREBOARD---------");
		$display("No. of Transactions:				%d",count[ARBITRATE]);
		$display("No. of Transactions Re-attempted:		%d",count[ERROR_TRANSMIT]);
		$display("No. of Transactions Successful:		%d",(count[ARBITRATE]-count[ERROR_TRANSMIT]));
		$display("Success Percent:				%d",100*(count[ARBITRATE]-count[ERROR_TRANSMIT])/count[ARBITRATE]);
		`ifdef DEBUG
		$display("HDL Output Queue:%p",Output_queue.size()); 
		`endif
	end
	`endif



	//Input Pipe Instantiation 

	scemi_input_pipe #(.BYTES_PER_ELEMENT((DATA_SIZE/8)),
                   .PAYLOAD_MAX_ELEMENTS((DATA_SIZE/8)),
                   .BUFFER_MAX_ELEMENTS(100)
                   ) inputpipe_data(clock);
	
	scemi_input_pipe #(.BYTES_PER_ELEMENT((Total_Nodes*2)),
                   .PAYLOAD_MAX_ELEMENTS((10)),
                   .BUFFER_MAX_ELEMENTS(100)
                   ) inputpipe_id(clock);
				   
				   
	//Output Pipe Instantiation 

	scemi_output_pipe #(.BYTES_PER_ELEMENT((DATA_SIZE/8)),
					   .PAYLOAD_MAX_ELEMENTS(1),
					   .BUFFER_MAX_ELEMENTS(1)
					   ) outputpipe(clock);

	//XRTL FSM to obtain operands from the HVL side
	logic [(DATA_SIZE)-1:0]packets;
	logic [(Total_Nodes*2*8)-1:0] Input_ID;
	bit eop=0;
	logic [7:0] ne_valid=0;
	
	initial
	begin
	@(posedge clock)
	 inputpipe_id.receive(1,ne_valid,Input_ID,eop);
	 for(int i=0;i<=Total_Nodes;i++)
	 ID[i]<=Input_ID[i*11+:11];
	 end

	always@(posedge clock)	
	for(int i=0;i<=(Total_Nodes-1);i++) begin
	if(data_out_req[i])	
	begin 
	outputpipe.send(1,Rx_packet[i],1); 
	`ifndef VELOCE
	Output_queue.push_front(Rx_packet[i]);
	`endif
	end
	end
	
	always@(negedge clock)
	begin
        if(reset)	packets <= {DATA_SIZE{1'b0}};
        else
        begin
			if(|data_in_req && ~(|Retransmit))	
			begin 
			inputpipe_data.receive(1,ne_valid,packets,eop);
			`ifndef VELOCE
			Input_queue.push_front(packets);
			`endif
			end
			for(int i=0;i<=(Total_Nodes-1);i++)
			begin
				if(data_in_req[i])	
				begin
					 In_packet[i]=packets;
					 Tx_ID[i]=ID[i];
				end
				else if(Retransmit[i])   Tx_ID[i]=0;
					 if((i%2))Rx_ID[i-1]=Tx_ID[i];
					 else	  Rx_ID[i+1]=Tx_ID[i];
			
			end
               
                 
        end
         
        
	end

endmodule


`include "def.pkg"

module clock_gen(output bit clock);
//tbx clkgen
  initial
	forever #CLOCK_WIDTH clock=~clock;
endmodule