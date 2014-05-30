//
// Interface to connect multiple CAN controllers
//


interface bus(input bit clk); //, input bit reset);



wand data;					// 1 bit data bus
logic bit_stuffing_EN;		// Enable bit stuffing check
logic ACK;
logic reset;

assign data=1'b1;




clocking cb @(posedge clk);
 
inout data;

endclocking


modport TEST (clocking cb,
			  inout data,
			  output clk,
			  input reset,
			  input bit_stuffing_EN,
			  input ACK);
			  
			  
modport Monitor( output data,
				 output clk,
				 output ACK,
				 output reset,
				 output bit_stuffing_EN);
			  
			  			  
endinterface

			 