// 
// DESCRIPTION: Monitor module runs concurrent assertions for error detection on CAN bus.
// Disabled in veloce mode
//

module Monitor( interface bus,
				input bit clock,
				input bit  ACK,
				input bit BIT_CHK,
				input reset);


//Internal Counters for assertion scoreboard				
int idle_check_Passcount,idle_check_Failcount;
int bit_check_Passcount,bit_check_Failcount;
int EOF_check_Passcount,EOF_check_Failcount;
int ACK_check_Passcount,ACK_check_Failcount;
int ACK_delimiter_Passcount,ACK_delimiter_Failcount;
int CRC_delimiter_Passcount,CRC_delimiter_Failcount;
int Overload_check_Passcount,Overload_check_Failcount;				

// Property definitions
//Assert various CAN Frame properties like Fixed field values,ACK Slot,Delimiters etc.
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
( ACK |-> bus.data)	;				// Read the value on the data bus at the same clk edge		
endproperty 	

property Overload_check;
@(posedge clock) disable iff (reset)
( $rose(ACK) |-> ##9 bus.data[*3])	;	//Check if bus goes dominant during IDLE phase				
endproperty

 

// Assert properties
//Internal counters to track pass and fails
assert property(Overload_check)
Overload_check_Passcount++;
else
Overload_check_Failcount++;	
	
assert property(CRC_delimiter_check)
CRC_delimiter_Passcount++;
else
CRC_delimiter_Failcount++;
				
assert property(bit_stuffing_check_high)
bit_check_Passcount++;
else
bit_check_Failcount++;

assert property(bit_stuffing_check_low)
bit_check_Passcount++;
else
bit_check_Failcount++;

assert property(bus_idle_check)
idle_check_Passcount++;
else
idle_check_Failcount++;
		
assert property(EOF_check)
EOF_check_Passcount++;
else
EOF_check_Failcount++;	

assert property(ACK_check)
ACK_check_Passcount++;
else
ACK_check_Failcount++;

assert property(ACK_delimiter_check)

ACK_delimiter_Passcount++;
else
ACK_delimiter_Failcount++;




final
begin
$display( "------------------------------------------------------------------------------------------------------");
$display( "----------------------------------------ASSERTION SCOREBOARD------------------------------------------");
$display("******************************************************************************************************");
$display(  "TYPE OF CHECK\t\t\t\tTOTAL COUNT\t\tPASS COUNT\t\tFAIL COUNT ");
$display( "------------------------------------------------------------------------------------------------------");
$display( " Bus IDLE Check\t\t%d\t\t%d\t\t%d      ", (idle_check_Passcount+idle_check_Failcount),idle_check_Passcount,idle_check_Failcount);
$display( " Bit Stuffing Check\t\t%d\t\t%d\t\t%d      ", (bit_check_Passcount+bit_check_Failcount),bit_check_Passcount,bit_check_Failcount);
$display( " CRC Delimiter check\t\t%d\t\t%d\t\t%d      ", (CRC_delimiter_Passcount+CRC_delimiter_Failcount),CRC_delimiter_Passcount,CRC_delimiter_Failcount);
$display( " ACK Check\t\t\t%d\t\t%d\t\t%d      ", (ACK_check_Passcount+ACK_check_Failcount),ACK_check_Passcount,ACK_check_Failcount);
$display( " ACK Delimiter Check\t\t%d\t\t%d\t\t%d      ", (ACK_delimiter_Passcount+ACK_delimiter_Failcount),ACK_delimiter_Passcount,ACK_delimiter_Failcount);
$display( " EOF Check\t\t\t%d\t\t%d\t\t%d      ", (EOF_check_Passcount+EOF_check_Failcount),EOF_check_Passcount,EOF_check_Failcount);
$display( " Overload Check\t\t%d\t\t%d\t\t%d      ", (Overload_check_Passcount+Overload_check_Failcount),Overload_check_Passcount,Overload_check_Failcount);
$display("*******************************************************************************************************");
end
endmodule
