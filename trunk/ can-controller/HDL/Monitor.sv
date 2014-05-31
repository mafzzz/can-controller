// 
// Monitor
//

module Monitor( interface bus,
				input bit clock,
				input bit  ACK,
				input bit BIT_CHK,
				input reset);



// Property definition

property bus_idle_check;
@(posedge clock) $rose(reset)|=> bus.data;
endproperty

property  bit_stuffing_check_high;
@(posedge clock) disable iff (!BIT_CHK)
(bus.data[*5] |=>  !bus.data)  ;      
endproperty	

property  bit_stuffing_check_low;
@(posedge clock) disable iff (!BIT_CHK)
(!bus.data[*5] |=> bus.data)  ;       
endproperty	

property EOF_check;						// End of Frame check
@(posedge clock) disable iff (reset)
( $rose(ACK) |-> ##2 bus.data[*7])	;					
endproperty

property ACK_check;
@(posedge clock) disable iff (reset)
( ACK |=> !bus.data)	;					
endproperty 

property ACK_delimiter_check;
@(posedge clock) disable iff (reset)
( ACK |=> ##1 bus.data)	;					
endproperty 


property CRC_delimiter_check;
@(posedge clock) disable iff (reset)
( ACK |-> bus.data)	;				// Read the value on the data bus at the previous clk edge		
endproperty 	

property Overload_check;
@(posedge clock) disable iff (reset)
( $rose(ACK) |-> ##9 bus.data[*3])	;					
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
$strobe( $time, " bit_stuffing_check_high Passed");
else
$error(" Bit Stuffing_high error");

assert property(bit_stuffing_check_low)
$strobe( $time, " bit_stuffing_check_low Passed");
else
$error(" Bit Stuffing_low error");

assert property(bus_idle_check)
$strobe( $time, " bus_idle_check Passed");
else
$error(" Bus not IDLE after Reset");

		
assert property(EOF_check)
$strobe( $time, " EOF check Passed");
else
$error(" End of Frame error");		

assert property(ACK_check)
$strobe( $time, " ACK_check Passed");
else
$error(" ACK_check Error");

assert property(ACK_delimiter_check)
$strobe( $time, " ACK_delimiter_check Passed");
else
$error(" ACK Delimiter Error");


endmodule
