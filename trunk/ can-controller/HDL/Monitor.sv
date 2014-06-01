// 
// Monitor
//

module Monitor( interface bus,
				input bit clock,
				input bit  ACK,
				input bit BIT_CHK,
				input reset);


				
int idle_check_Passcount,idle_check_Failcount;
int bit_check_Passcount,bit_check_Failcount;
int EOF_check_Passcount,EOF_check_Failcount;
int ACK_check_Passcount,ACK_check_Failcount;
int ACK_delimiter_Passcount,ACK_delimiter_Failcount;
int CRC_delimiter_Passcount,CRC_delimiter_Failcount;
int Overload_check_Passcount,Overload_check_Failcount;				

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
//$strobe( $time, " Overload_check Passed");
Overload_check_Passcount++;
else
//$error(" Overload  error");
Overload_check_Failcount++;	
	
assert property(CRC_delimiter_check)
//$strobe( $time, " CRC delimiter check Passed");
CRC_delimiter_Passcount++;
else
//$error(" CRC Delimiter Error");
CRC_delimiter_Failcount++;
				
assert property(bit_stuffing_check_high)
//$strobe( $time, " bit_stuffing_check_high Passed");
bit_check_Passcount++;
else
//$error(" Bit Stuffing_high error");
bit_check_Failcount++;

assert property(bit_stuffing_check_low)
//$strobe( $time, " bit_stuffing_check_low Passed");
bit_check_Passcount++;
else
//$error(" Bit Stuffing_low error");
bit_check_Failcount++;

assert property(bus_idle_check)
//$strobe( $time, " bus_idle_check Passed");
idle_check_Passcount++;
else
//$error(" Bus not IDLE after Reset");
idle_check_Failcount++;
		
assert property(EOF_check)
//$strobe( $time, " EOF check Passed");
EOF_check_Passcount++;
else
//$error(" End of Frame error");	
EOF_check_Failcount++;	

assert property(ACK_check)
//$strobe( $time, " ACK_check Passed");
ACK_check_Passcount++;
else
//$error(" ACK_check Error");
ACK_check_Failcount++;

assert property(ACK_delimiter_check)
//$strobe( $time, " ACK_delimiter_check Passed");

ACK_delimiter_Passcount++;
else
//$error(" ACK Delimiter Error");
ACK_delimiter_Failcount++;




final
begin

$display("*****************************************************************************");
$display(  "TYPE OF CHECK				TOTAL COUNT 		PASS COUNT    FAIL COUNT ");
$display( "---------------------------------------------------------------------------");
$display( " Bus IDLE Check					%0d					%0d           %0d      ", (idle_check_Passcount+idle_check_Failcount),idle_check_Passcount,idle_check_Failcount);
$display( " Bit Stuffing Check 				%0d					%0d           %0d      ", (bit_check_Passcount+bit_check_Failcount),bit_check_Passcount,bit_check_Failcount);
$display( " CRC Delimiter check				%0d					%0d           %0d      ", (CRC_delimiter_Passcount+CRC_delimiter_Failcount),CRC_delimiter_Passcount,CRC_delimiter_Failcount);
$display( " ACK Check						%0d					%0d           %0d      ", (ACK_check_Passcount+ACK_check_Failcount),ACK_check_Passcount,ACK_check_Failcount);
$display( " ACK Delimiter Check				%0d					%0d           %0d      ", (ACK_delimiter_Passcount+ACK_delimiter_Failcount),ACK_delimiter_Passcount,ACK_delimiter_Failcount);
$display( " EOF Check						%0d					%0d           %0d      ", (EOF_check_Passcount+EOF_check_Failcount),EOF_check_Passcount,EOF_check_Failcount);
$display( " Overload Check					%0d					%0d           %0d      ", (Overload_check_Passcount+Overload_check_Failcount),Overload_check_Passcount,Overload_check_Failcount);
$display("*****************************************************************************");

endmodule
