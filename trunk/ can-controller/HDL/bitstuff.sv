`include "def.pkg"

module bitstuff_gen(
input logic clock,bitgen_en,data,
output  logic bit_stuff
);

int count1,count0;
always_ff@ (negedge clock)
begin
if(bitgen_en)
begin
		if(data)
			begin
				if(count1==STUFF_COUNT)
					begin
						bit_stuff<=1'b1;
						count1<=0;
					end
				else 
					begin
						count1<=count1+1'b1;
						{bit_stuff,count0}<=0;
					end
			end
		else
			begin
				if(count0==STUFF_COUNT)
					begin
						bit_stuff<=1'b1;
						count0<=0;
					end
				else
					begin
						count0<=count0+1'b1;
						{bit_stuff,count1}<=0;
					end
		end

end
else
	{count1,count0,bit_stuff}<=0;
end
endmodule

`include "def.pkg"

module bitstuff_chk(
input logic clock,bitchk_en,data,
output  logic Stuff_error
);

int count1,count0;
always_ff@ (negedge clock)
begin
if(bitchk_en)
begin
		if(data)
			begin
				if(count1==STUFF_COUNT+1)
					begin
						Stuff_error<=1'b1;
						count1<=0;
					end
				else 
					begin
						count1<=count1+1'b1;
						{Stuff_error,count0}<=0;
					end
			end
		else
			begin
				if(count0==STUFF_COUNT+1)
					begin
						Stuff_error<=1'b1;
						count0<=0;
					end
				else
					begin
					  Stuff_error<=1'b0;
						count0<=count0+1'b1;
						{Stuff_error,count1}<=0;
					end
			end

end
else
	{count1,count0,Stuff_error}<=0;
end

endmodule