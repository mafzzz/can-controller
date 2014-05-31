`include "def.pkg"


module top();
	bit clock;
	bit reset;
	
	logic [Total_Nodes-1:0] data_in_req,data_out_req,data,Retransmit;
	bit [DATA_SIZE-1:0] In_packet[0:Total_Nodes-1],Rx_packet[0:Total_Nodes-1];
	bit [ID_SIZE-1:0] Tx_ID[0:Total_Nodes-1], Rx_ID[0:Total_Nodes-1];
	
	 bit [ID_SIZE-1:0] ID[0:Total_Nodes-1]='{11'h001,11'h7FF,11'h111,11'h10A};
	longint	input_data[]='{64'hFFFFEEEE0000FEF1,64'hAAAABBBBCCCC0021};
	longint	output_data[$];
	int	count[int]='{default:0};
	bit preserve_id=0;
	
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
	 
	
	 
	
	
	
	
	always@(negedge clock)
	begin
	for(int i=0;i<=(Total_Nodes-1);i++)
		begin
			if(data_in_req[i])	
			begin
				 In_packet[i]<=input_data[i%2];
				 Tx_ID[i]<=ID[i];
				 if(preserve_id)
				 begin
					 Rx_ID[i]<=Rx_ID[i];
					 preserve_id<=0;
				 end
				 else  Rx_ID[i]<=(i%2)?ID[i-1]:ID[i+1];
			end
			else if(data_out_req[i])	output_data.push_front(Rx_packet[i]);
			else if(Retransmit[i])   
			begin
				Tx_ID[i]=0;
				if(i%2) Rx_ID[i-1]=0;
				  else  Rx_ID[i+1]=0;
				preserve_id<=1;
			end
		end
	end
	
	always_comb
	count[c0.state]=count[c0.state]+1;
	
	initial
	begin
	reset=1'b1;
	repeat(2)  @(negedge clock); reset=~reset;
	end
	
	final
	begin
	$display("No. of Transactions Attempted:\t%p",count[ARBITRATE]);
	$display("No. of Failed Bus Transactions:\t%p",count[ERROR_TRANSMIT]);
	$display("No. of Successful Bus Transactions:\t%p",(count[ARBITRATE]-count[ERROR_TRANSMIT]));
	$display("Success Percent:\t%p",100*(count[ARBITRATE]-count[ERROR_TRANSMIT])/count[ARBITRATE]);
	$display("%p",count);
	end
endmodule

`include "def.pkg"

module clock_gen(output bit clock);
  initial
	forever #CLOCK_WIDTH clock=~clock;
	endmodule
	