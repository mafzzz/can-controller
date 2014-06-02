
//
//DESCRIPTION:
//BitStuff module Flags when certain 'count' of successive 1's/0's
//are seen on can bus
//
//For Master mode it signals when 5 consecutive 1's/0's are seen to inform master to 'stuff' next bit
//For Slave mode it signals when 6 consecutive 1's/0's are seen to inform slave of Stuff error on bus
//

`include "def.pkg"

module bitstuff #(parameter Thresh_Count=0)(	//Thresh_count==5 for bitstuff_chk & ==6 for stuff_error
input logic clock,enable,data,					//Input signals from CAN node
output  logic flag								//Output flag when threshold reached
);

int count1=1,count0=1;							//Counter for tracking successive 1's/0's 

//Procedural block
always_ff@ (negedge clock)
begin
if(enable)										//If enable asserted
begin
		assert(data)
			begin
				if(count1==Thresh_Count)		//If hit threshold flag
					begin
						flag<=1'b1;
						count1<=0;
					end
				else 							//Else Increment
					begin
						count1<=count1+1'b1;
						{flag,count0}<=0;
					end
			end
		else
			begin
				if(count0==Thresh_Count)
					begin
						flag<=1'b1;
						count0<=0;
					end:0's Check
				else
					begin
						count0<=count0+1'b1;
						{flag,count1}<=0;
					end
		end

end
else
	{count1,count0,flag}<=0;					//Enable signal de-asserted
end
endmodule