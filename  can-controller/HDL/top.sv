`include "def.pkg"

interface can_bus(input [Total_Nodes-1:0] input_data);
wire data = (1'b1 & (&input_data));
endinterface


module top();
	bit clock;
	bit reset;
	logic [Total_Nodes-1:0] data_in_req;
	logic [Total_Nodes-1:0] data_out_req;
	logic [Total_Nodes-1:0] data;
	bit [DATA_SIZE-1:0] In_packet[0:Total_Nodes-1],Rx_packet[0:Total_Nodes-1];
	bit [ID_SIZE-1:0] Tx_ID[0:Total_Nodes-1], Rx_ID[0:Total_Nodes-1];
	bit [ID_SIZE-1:0] ID[0:1]='{11'h001,11'h7FF};
	longint	input_data[]='{64'hFFFFEEEE0000FEF1,64'hAAAABBBBCCCC0020};
	longint	output_data[$];
	state_t state;
	int	count[int]='{default:0};
	
	can_bus bus (data);
	
	can		c0(.*,.In_packet(In_packet[0]),.Rx_packet(Rx_packet[0]),.Tx_ID(ID[0]),.Rx_ID(ID[1]),
	                             .data_in_req(data_in_req[0]),.data_out_req(data_out_req[0]),.data(data[0]));
	can		c1(.*,.In_packet(In_packet[1]),.Rx_packet(Rx_packet[1]),.Tx_ID(ID[1]),.Rx_ID(ID[0]),
	                             .data_in_req(data_in_req[1]),.data_out_req(data_out_req[1]),.data(data[1]));
	
	initial
	begin
	clock=1'b0;
	forever #10 clock=~clock;
	end
	
	
	always@(negedge clock)
	begin
	for(int i=0;i<=(Total_Nodes-1);i++)
		begin
			if(data_in_req[i])	 In_packet[i]=input_data[i%2];
			else if(data_out_req[i])	output_data.push_front(Rx_packet[i]);
		end
	end
	
	always_comb
	count[c1.state]=count[c1.state]+1;
	
	initial
	begin
	reset=1'b1;
	#20 reset=~reset;
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
	