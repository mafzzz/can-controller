//
// Top module
//


module top;

bit clk;
bit reset;

bus data_bus(.clk(clk)); //,.reset(reset));

clk_generator C1(.clk(clk));
testbench T1(.bus_if(data_bus.TEST));
Monitor M1(.bus_if(data_bus.Monitor));	


endmodule
