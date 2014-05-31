
//DUT Verilog

`include "def.pkg"
 
module can    
  ( input [DATA_SIZE-1:0] In_packet,
	input clock,
	input reset,
	input [ID_SIZE-1:0] Tx_ID,Rx_ID,
	can_bus bus,
	output logic data_in_req,
	output logic data_out_req,
	output logic [DATA_SIZE-1:0] Rx_packet,
	output logic data,
	output logic Retransmit,
	`ifdef ASSERT_EN
	output logic SLAVE_ACK,
	output logic bitchk_en
	`endif
  );
  

  
  logic   [DATA_CRC_LEN:0]	CRC_array;
  logic [CRC_SIZE-1:0] CRC_chk;
  int CRC_Len;
  
  logic	  [DATA_FRAME_SIZE:0]	Serial_stream;
  logic [DATA_SIZE-1:0] Tx_packet;
  Can_packet	packet;
  state_t state;
  
  Error_Frame	Error_packet;
  int Tx_Ecount,Rx_Ecount;
  errorstate_t error;
  
  
  int i,Serial_count,crc_count,count;
  bit BIT_ERROR,ARB_LOSS,ACK_ERROR,CRC_CHK,SLAVE_EOF,bit_stuff,Stuff_error;
  bit bitgen_en;
  
  `ifndef ASSERT_EN
	logic SLAVE_ACK,logic bitchk_en;
	`endif

 
 bitstuff_gen	bit_gen1(clock,bitgen_en,bus.data,bit_stuff);
 bitstuff_chk	bit_chk1(clock,bitchk_en,bus.data,Stuff_error);
 

			
 always_ff @(posedge clock)
 begin
	if(reset) 
	 begin
		{data_in_req,Tx_packet,Tx_Ecount,Rx_Ecount,Retransmit}<=0;
		 state<=BUS_RST;error<=ACTIVE;
		 data<=`REC;
	 end
	else
	 begin
		unique case (state)
		
		BUS_RST:		begin
							data<=`REC;data_out_req<=0;data_in_req<=~Retransmit;
							{BIT_ERROR,ARB_LOSS,ACK_ERROR,CRC_CHK,SLAVE_ACK,SLAVE_EOF}<='0;
							{i,count,Serial_count,crc_count}<='0;
							{CRC_array,bitgen_en,bitchk_en}<='0;
							state<=READ_PACKET;
						end
						
		READ_PACKET:  	begin 
							if(!In_packet)	state<=BUS_RST;
							else if(data_in_req) Tx_packet<=In_packet;
							{data_in_req,Retransmit}<='0;
							state<=FORMAT_PACKET;
						end
	                       				
		FORMAT_PACKET: 	begin	
							if(`DATA_PACKET) 	Data_Frame_Pack(packet);
							else 				Req_Frame_Pack(packet);
							state<=CRC_GEN;
						end
						
		CRC_GEN: 		begin
							if(`DATA_PACKET)
							begin
								CRC_array={packet.Data.Data,packet.Data.DLC,packet.Data.R0,packet.Data.IDE,packet.Data.RTR,packet.Data.ID,packet.Data.SOF};
								bus.CRC_gen(.CRC_array(CRC_array),.CRC_Len(CRC_Len),.CRC_RG(packet.Data.CRC));
								`ifdef ERROR_INJECT
								//if(`ERROR_FLAG)
								packet.Data.CRC<={<<{packet.Data.CRC}};
								`endif
							end
							else
							begin
								CRC_array={packet.Req.DLC,packet.Req.R0,packet.Req.IDE,packet.Req.RTR,packet.Req.ID,packet.Req.SOF};
								bus.CRC_gen(.CRC_array(CRC_array),.CRC_Len(CRC_Len),.CRC_RG(packet.Req.CRC));
								`ifdef ERROR_INJECT
								//if(`ERROR_FLAG)
								packet.Req.CRC<={<<{packet.Req.CRC}};
								`endif
							end
							state<=BIT_SERIALIZE;
						end

		BIT_SERIALIZE:	begin
							Serial_stream<=`DATA_PACKET?packet.Data:packet.Req;
							Serial_count<=`DATA_PACKET?DATA_FRAME_SIZE:REQ_FRAME_SIZE;
							CRC_array<=0;
							state<=BUS_IDLE_CHECK;
						end

		BUS_IDLE_CHECK:	begin
							if(bus.data)
							begin
								if(count==BUS_IDLE_COUNT)
								begin
									state<=ARBITRATE;
									{bitgen_en,bitchk_en}<='1;
								end
								else	count<=count+1'b1;
							
							end
							else 	state<=Tx_ERROR;
						end
						
		ARBITRATE:		begin
							if(Stuff_error)	state<=Tx_ERROR;
							else if(bit_stuff)	data<=~data;
							else if(ARB_LOSS)
							begin
								state<=SLAVE;
								data<=`REC;
							end
							else if(i<=ARB_LENGTH)
							begin
								data<=Serial_stream[i];
								i<=i+1;
							end
					
						end
					
						
		MASTER:			begin
							if(BIT_ERROR ||  ACK_ERROR || Stuff_error)	state<=Tx_ERROR;
							else if(i<=Serial_count)
							begin
								if(bit_stuff)	data<=~data;
								else
								begin
									data<=Serial_stream[i];
									state<=(i==Serial_count)?IFS:MASTER;
									i<=i+1'b1;
								end
							end
						end
						

		IFS:			begin
							if(i<=(Serial_count+IFS_LENGTH))	
							begin
								if(i==(Serial_count+IFS_LENGTH))
								begin
									state<=BUS_RST;
									Tx_Ecount<=Tx_Ecount-1'b1;
									if(Tx_Ecount<=ACTIVE_THRESHOLD) error=ACTIVE;
								end
								else
								begin
									data<=`REC;
									i<=i+1'b1;
								end
							end
						end

		SLAVE:			begin
							if(Stuff_error)		state<=Rx_ERROR;
							else if(i==(CRC_Len+1'b1))
							begin
								CRC_CHK<=1'b1;
								bus.CRC_gen(.CRC_array(CRC_array),.CRC_Len(CRC_Len),.CRC_RG(CRC_chk));
								crc_count<=0;
							end
							else if(SLAVE_ACK)
							begin
								data<=`DOM;
								{bitgen_en,bitchk_en}<=0;
								SLAVE_EOF<=1'b1;
								count<=0;
							end
							else if(SLAVE_EOF && count==1)data<=`REC;
						end
					
	
						
					
		Tx_ERROR:		begin
							Retransmit=1'b1;
							Serial_count=FLAG_SIZE+DELIM_SIZE-1;
							{Serial_stream,i}=0;
							data<=`DOM;
							bus.Error_Handle(error,Tx_Ecount,Error_packet);
							Serial_stream=Error_packet;
							state=ERROR_TRANSMIT;
							if(Tx_Ecount>=ACTIVE_THRESHOLD)	error=PASSIVE;
							if(Tx_Ecount>=PASSIVE_THRESHOLD) state=BUS_OFF;
						end
		
		
		Rx_ERROR:		begin
							Serial_count=FLAG_SIZE+DELIM_SIZE-1;
							{Serial_stream,i}=0;
							data<=`DOM;
							bus.Error_Handle(error,Rx_Ecount,Error_packet);
							Serial_stream=Error_packet;
							state=ERROR_TRANSMIT;
							if(Rx_Ecount>=ACTIVE_THRESHOLD)	error=PASSIVE;
						end		
						
		ERROR_TRANSMIT:	begin
							if(i<=Serial_count-DELIM_SIZE)
							begin
								data<=Serial_stream[i];
								i<=i+1'b1;
							end
							else if(i>(Serial_count-DELIM_SIZE))
							begin
								if(!bus.data) data<=`REC;
								else
								begin
									data<=Serial_stream[i];
									i<=i+1;
								end
							end
							state<=(i==Serial_count && bus.data)?BUS_RST:ERROR_TRANSMIT;
						end
						
		BUS_OFF:		begin state<=BUS_OFF;data<=`REC; end
		 
		 endcase
	 end
 end
 
 always_ff @(negedge clock)
 begin
 case(state)
						
 ARBITRATE:		begin
					if(bit_stuff)	CRC_array<=CRC_array;
					else
					begin
						CRC_array[i-1]<=bus.data;
						ARB_LOSS=(data==bus.data)?0:1;
						if(i==ARB_LENGTH+1 && !ARB_LOSS) state<=MASTER;
				    else if(ARB_LOSS)
						begin
							state<=SLAVE;
							data<=`REC;
						end
					end 
				end

 MASTER:		begin
					if(( (`DATA_PACKET) && (i!=DATA_ACK_SLOT) ) || ( (!`DATA_PACKET) && (i!=REQ_ACK_SLOT)) )
							BIT_ERROR=(data==bus.data)?0:1;
					else if(( (`DATA_PACKET) && (i==DATA_ACK_SLOT) ) || ( (!`DATA_PACKET) && (i==REQ_ACK_SLOT)))
						begin
							ACK_ERROR=bus.data;
							{bitgen_en,bitchk_en}<=0;
						end
				end
				
IFS:  			assert(bus.data)
				else state<=Tx_ERROR;
						
SLAVE:			begin
					if(i<=CRC_Len && !bit_stuff && !CRC_CHK && !SLAVE_EOF)
						begin
							CRC_array[i]<=bus.data;
							if(i>ARB_LENGTH) CRC_Len=`RTR_BIT?REQ_CRC_LEN:DATA_CRC_LEN;
							i<=i+1'b1;
						end
						
					else if(bit_stuff) 
						begin
							CRC_array<=CRC_array;
							CRC_chk<=CRC_chk;
						end
						
					else if(CRC_CHK)
						begin
							if(crc_count<=CRC_SIZE-1)
							begin
							  i<=0;
								assert (CRC_chk[crc_count]==bus.data) crc_count<=crc_count+1'b1;
								else state<=Rx_ERROR;
							end
							else
							begin	
								if(bus.data) 
								begin 
									CRC_CHK<=0; 
									SLAVE_ACK<=1'b1; 
								end
								else	state<=Rx_ERROR; 		//CRC DELIM ERROR
							end	
						end
						
					else if(SLAVE_EOF)
					begin
						
						SLAVE_ACK<=0;
						count<=count+1'b1;
						if(count >=1 && !bus.data) state<=Rx_ERROR;
						if(count==(EOF_SIZE+BUS_IDLE_COUNT) && bus.data)
							begin
								if(!CRC_array[`RTR_BIT] && CRC_array[ID_SIZE:1]=={<<{Rx_ID}})
									begin
											data_out_req<=1'b1;
											{<<{Rx_packet}}<=CRC_array[(DATA_SIZE+DATA_START-1):DATA_START];
									end
								state<=BUS_RST;
								if(Rx_Ecount>=ACTIVE_THRESHOLD)	Rx_Ecount<=ACTIVE_THRESHOLD-ERROR_STEP;
								else	if (Rx_Ecount) 			Rx_Ecount<=Rx_Ecount-1'b1;
							end
					
					end
				end
					

endcase
end

task automatic Data_Frame_Pack(ref Can_packet packet);
	{packet.Data.SOF,packet.Data.RTR,packet.Data.IDE,packet.Data.R0,packet.Data.CRC}<='0;
	{packet.Data.CRC_Delim,packet.Data.ACK,packet.Data.ACK_Delim,packet.Data.EOF}<='1;
	packet.Data.ID<={<<{Tx_ID}};packet.Data.Data<={<<{Tx_packet}};packet.Data.DLC<={<<{DLC}};
endtask
 
task automatic Req_Frame_Pack(ref Can_packet packet);
	{packet.Req.SOF,packet.Req.IDE,packet.Req.R0,packet.Req.CRC}<='0;
	{packet.Req.CRC_Delim,packet.Req.ACK,packet.Req.ACK_Delim,packet.Req.EOF,packet.Req.RTR}<='1;
	packet.Req.DLC<={<<{DLC}};packet.Req.ID<={<<{Rx_ID}};
endtask	
					
endmodule


