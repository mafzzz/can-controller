`include "def.pkg"


module bitstuff #(parameter Thresh_Count=0)(
input logic clock,enable,data,
output  logic flag
);

int count1=1,count0=1;
always_ff@ (negedge clock)
begin
if(enable)
begin
		assert(data)
			begin
				if(count1==Thresh_Count)
					begin
						flag<=1'b1;
						count1<=0;
					end
				else 
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
					end
				else
					begin
						count0<=count0+1'b1;
						{flag,count1}<=0;
					end
		end

end
else
	{count1,count0,flag}<=0;
end
endmodule