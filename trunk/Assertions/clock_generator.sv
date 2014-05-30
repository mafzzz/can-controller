//
// Clock generator
//

module clk_generator( output bit clk);

bit clock=0;					// local clock
assign clk =clock;
initial
begin

	forever #2ns clock=~clock;
end

endmodule
