// 
// Monitor
//

module Monitor( interface bus_if);



// Property definition

property bus_idle_check;
@(posedge bus_if.clk) $rose(bus_if.reset)|-> bus_if.data;
endproperty

property  bit_stuffing_check_high;
@(posedge bus_if.clk) disable iff (!bus_if.bit_stuffing_EN)
(bus_if.data[*5] |->  !bus_if.data)  ;      
endproperty	

property  bit_stuffing_check_low;
@(posedge bus_if.clk) disable iff (!bus_if.bit_stuffing_EN)
(!bus_if.data[*5] |-> bus_if.data)  ;       
endproperty	

property EOF_check;						// End of Frame check
@(posedge bus_if.clk) disable iff (bus_if.reset)
( $rose(bus_if.ACK) |-> bus_if.data[*7])	;					
endproperty

property ACK_delimiter_check;
@(posedge bus_if.clk) disable iff (bus_if.reset)
( !bus_if.ACK |-> bus_if.data)	;					
endproperty 


property CRC_delimiter_check;
@(posedge bus_if.clk) disable iff (bus_if.reset)
( !bus_if.ACK |-> $past(bus_if.data))	;				// Read the value on the data bus at the previous clk edge		
endproperty 	

property Overload_check;
@(posedge bus_if.clk) disable iff (bus_if.reset)
( $rose(bus_if.ACK) |-> ##6 bus_if.data[*3])	;					
endproperty



// Assert properties
	
assert property(Overload_check)
$strobe( $time, " Overload_check Passed");
else
$error(" Overload  error");
	
	
assert property(CRC_delimiter_check)
$strobe( $time, " CRC delimiter check Passed");
else
$error(" CRC Delimiter Error");

				
assert property(bit_stuffing_check_high)
else
$error(" Bit Stuffing_high error");

assert property(bit_stuffing_check_low)
else
$error(" Bit Stuffing_low error");

assert property(bus_idle_check)
else
$error(" Bus not IDLE after Reset");

		
assert property(EOF_check)
$strobe( $time, " EOF check Passed");
else
$error(" End of Frame error");		

assert property(ACK_delimiter_check)
$strobe( $time, " ACK_delimiter_check Passed");
else
$error(" ACK Delimiter Error");


endmodule
