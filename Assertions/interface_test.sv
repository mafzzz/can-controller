//
// Testbench to verify behaviour of the bus
//

program testbench(interface bus_if);

initial
begin
	$monitor($time,"  clk=%b  Reset= %b  ACK= %b  Data=%b" ,bus_if.clk,bus_if.reset,bus_if.ACK,bus_if.cb.data);
	

	bus_if.ACK<=1'b1;
    
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b0;
	
	
	@bus_if.cb;
	bus_if.reset<=1'b0;
	bus_if.cb.data<=1'b0;
	bus_if.ACK<=1'b1;
	
	
	@bus_if.cb;
	bus_if.reset<=1'b1;
	bus_if.ACK<=1'b0;
	bus_if.cb.data<=1'b0;
	
	
	@bus_if.cb;
	bus_if.reset<=1'b0;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	@bus_if.cb;
	bus_if.ACK<=1'b1;
	bus_if.cb.data<=1'b1;
	
	
	
	#5ns $finish;


	end 

endprogram