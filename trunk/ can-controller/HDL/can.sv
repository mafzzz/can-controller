//
//Description:Synthesizable DUT. Implements FSM for Node operation
//

`include "def.pkg"
 
 
module can    
  ( input [DATA_SIZE-1:0] In_packet,		//Input packet from Transactor
	input clock,						
	input reset,
	input [ID_SIZE-1:0] Tx_ID,Rx_ID,		//Acceptance filter ID's
	can_bus bus,							//Interface Instance
	output logic data_in_req,				//Signal to request data
	output logic data_out_req,				//Signal to output data
	output logic [DATA_SIZE-1:0] Rx_packet,	//Data received by CAN node if it was a slave
	output logic data,						//Node's serial data output line, will be AND'ed with other lines on the common data bus
	output logic Retransmit					//Flag that node behaving as master failed in its previous attempt to transmit data
	`ifdef ASSERT_EN
	,output logic SLAVE_ACK,				//Signals for Assertion based verification
	output logic bitchk_en
	`endif
  );
  

  //Internals for CRC array
  logic   [DATA_CRC_LEN:0]	CRC_array;		
  logic [CRC_SIZE-1:0] CRC_chk;
  int CRC_Len;
  
  logic	  [DATA_FRAME_SIZE:0]	Serial_stream;  //Serial stream to be output on bus
  logic [DATA_SIZE-1:0] Tx_packet;				//Internal storage for input packet
  Can_packet	packet;							//Union of Data & Req structs
  state_t state;								//enumerated FSM state variable
	
  Error_Frame	Error_packet;					//Struct for error packet
  int Tx_Ecount,Rx_Ecount;						//Error counters which control node's error status to go ACTIVE or PASSIVE
  errorstate_t error;							//enumerated error state variable
  
  
  int i,Serial_count,crc_count,count;			//Internal counts
  bit BIT_ERROR,ARB_LOSS,ACK_ERROR,CRC_CHK,SLAVE_EOF,bit_stuff,Stuff_error;		//Flags for various checks
  bit bitgen_en;					//Flag to Master to indicate a need to stuff next bit
  
  `ifndef ASSERT_EN
	logic SLAVE_ACK;				//Flags for SLAVE Acknowledgement if no CRC error 
	logic bitchk_en;				//Flag for Slave that bit-stuff error seen on bus
	`endif							

 //Instantiate Bitstuff Checker(used in Slave mode) and Generator(used in Master) mode
 bitstuff #(.Thresh_Count(STUFF_COUNT)) bitstuff_gen  (clock,bitgen_en,bus.data,bit_stuff);
 bitstuff #(.Thresh_Count(STUFF_COUNT+1)) bitstuff_chk  (clock,bitchk_en,bus.data,Stuff_error);
 

 //Generator Procedural Block- Performs Data Pack,Arbitration,Drive data line and initiate Error handle			
 always_ff @(posedge clock)
 begin
	if(reset) 
	 begin
		{data_in_req,Tx_packet,Tx_Ecount,Rx_Ecount,Retransmit}<=0;		//Global Reset
		 state<=BUS_RST;error<=ACTIVE;
		 data<=`REC;
	 end
	else
	 begin
		unique case (state)
		
		BUS_RST:		begin
							data<=`REC;data_out_req<=0;data_in_req<=~Retransmit;
							{BIT_ERROR,ARB_LOSS,ACK_ERROR,CRC_CHK,SLAVE_ACK,SLAVE_EOF}<='0;	    //Internal reset at end of transaction
							{i,count,Serial_count,crc_count}<='0;
							{CRC_array,bitgen_en,bitchk_en}<='0;
							state<=READ_PACKET;
						end
						
		READ_PACKET:  	begin 
							if(!In_packet)	state<=BUS_RST;				//If no data to transmit - reset
							else if(data_in_req) Tx_packet<=In_packet;		//else get data
							data_in_req<='0;
							state<=FORMAT_PACKET;
						end
	                       				
		FORMAT_PACKET: 	begin	
							if(`DATA_PACKET) 	Data_Frame_Pack(packet);		//Format packet into Data or Req frame
							else 				Req_Frame_Pack(packet);			//We have modelled this randomly through LSB check
							state<=CRC_GEN;										//As primary focus is to model the physical layer i.e. BUS 
						end															//operation and not the Application layer
																			
						
		CRC_GEN: 		begin
							if(`DATA_PACKET)									//Pack CRC array depending on frame type
							begin
								CRC_array={packet.Data.Data,packet.Data.DLC,packet.Data.R0,packet.Data.IDE,packet.Data.RTR,packet.Data.ID,packet.Data.SOF};
								bus.CRC_gen(.CRC_array(CRC_array),.CRC_Len(CRC_Len),.CRC_RG(packet.Data.CRC));		//Generate CRC field
								`ifdef ERROR_INJECT								//Flag to enable error mode
								if(`ERROR_FLAG)						//Injects random CRC errors which causes transmission to fail
								packet.Data.CRC=Retransmit?packet.Data.CRC:{<<{packet.Data.CRC}};		//Errors disabled for re-transmission
								`endif
							end
							else
							begin
								CRC_array={packet.Req.DLC,packet.Req.R0,packet.Req.IDE,packet.Req.RTR,packet.Req.ID,packet.Req.SOF};
								bus.CRC_gen(.CRC_array(CRC_array),.CRC_Len(CRC_Len),.CRC_RG(packet.Req.CRC));
							end
							state<=BIT_SERIALIZE;
							Retransmit<=0;
						end

		BIT_SERIALIZE:	begin
							Serial_stream<=`DATA_PACKET?packet.Data:packet.Req;			//Serialise the resulting stream into a bit vector
							Serial_count<=`DATA_PACKET?DATA_FRAME_SIZE:REQ_FRAME_SIZE;	
							CRC_array<=0;
							state<=BUS_IDLE_CHECK;
						end

		BUS_IDLE_CHECK:	begin
							assert(bus.data)			//Assert if bus is idle i.e. no dominant bits
							begin
								if(count==BUS_IDLE_COUNT)		//After idle threshold reached,arbitrate
								begin
									state<=ARBITRATE;
									{bitgen_en,bitchk_en}<='1;		//and enable bit-stuff, check modules
								end
								else	count<=count+1'b1;			//else increment count up to threshold
							
							end
							else 	state<=Tx_ERROR;			//If any time dominant bit detected during idle phase flag error
						end
						
		ARBITRATE:		begin										//Begin Arbitration along with checking data line after driving a bit 
							if(Stuff_error)	state<=Tx_ERROR;		//If stuff error,flag
							else if(bit_stuff)	data<=~data;		//If bit-stuff, flip data 
							else if(ARB_LOSS)										
							begin
								state<=SLAVE;						//If arbitration lost go to slave mode
								data<=`REC;
							end
							else if(i<=ARB_LENGTH)		//Else keep arbitrating (transfer to master state done in Checker procedural block)
							begin									
								data<=Serial_stream[i];
								i<=i+1;
							end
					
						end
					
						
		MASTER:			begin
							if(BIT_ERROR ||  ACK_ERROR || Stuff_error)	state<=Tx_ERROR;		//Flag errors
							else if(i<=Serial_count)						//Else keep transmitting data, stuff if needed
							begin
								if(bit_stuff)	data<=~data;
								else
								begin
									data<=Serial_stream[i];
									state<=(i==Serial_count)?IFS:MASTER;		//Once all data successfully transmitted wait for 
									i<=i+1'b1;													//InterFrameSpace interval
								end
							end
						end
							
						

		IFS:			begin
							if(i<=(Serial_count+IFS_LENGTH))				//IFS field, transmit recessive bits
							begin
								if(i==(Serial_count+IFS_LENGTH))
								begin
									state<=BUS_RST;							//Once done,get ready for next transaction
									Tx_Ecount<=Tx_Ecount-1'b1;					//Decrement Tx error count after successful bus transaction
									if(Tx_Ecount<=ACTIVE_THRESHOLD) error=ACTIVE;		//Check count against threshold
								end
								else
								begin
									data<=`REC;			//Loop for IFS field width
									i<=i+1'b1;
								end
							end
						end

		SLAVE:			begin
							if(Stuff_error)		state<=Rx_ERROR;			//If lost arbitration,enter slave mode
							else if(i==(CRC_Len+1'b1))						//Keep sampling data(done in negedge procedural block),
																					//Once payload sampled
							begin
								CRC_CHK<=1'b1;											
								bus.CRC_gen(.CRC_array(CRC_array),.CRC_Len(CRC_Len),.CRC_RG(CRC_chk));	//initiate CRC check for payload seen on bus
								crc_count<=0;
							end
							else if(SLAVE_ACK)				//If check successful, ACK by asserting Dominant bit during Transmitters ACK slot
							begin
								data<=`DOM;
								{bitgen_en,bitchk_en}<=0;
								SLAVE_EOF<=1'b1;				//Once ACK'ed wait until Master finishes transmitting EOF & IFS bits
								count<=0;
							end
							else if(SLAVE_EOF && count==1)data<=`REC;		//During wait phase drive recessive bits
						end
					
	
						
					
		Tx_ERROR:		begin
							Retransmit=1'b1;						//If error during Master mode, flag Retransmit 
							Serial_count=FLAG_SIZE+DELIM_SIZE-1;
							{Serial_stream,i}=0;					
							data<=`DOM;
							bus.Error_Handle(error,Tx_Ecount,Error_packet);  
							Serial_stream=Error_packet;						//Load serial stream with error bits
							state=ERROR_TRANSMIT;												
							if(Tx_Ecount>=ACTIVE_THRESHOLD)	error=PASSIVE;		//Check error counters and set error states
							if(Tx_Ecount>=PASSIVE_THRESHOLD) state=BUS_OFF;			//If crossed passive threshold take node off bus
						end
		
		
		Rx_ERROR:		begin
							Serial_count=FLAG_SIZE+DELIM_SIZE-1;		//If error during slave mode
							{Serial_stream,i}=0;
							data<=`DOM;
							bus.Error_Handle(error,Rx_Ecount,Error_packet);  //Load serial stream
							Serial_stream=Error_packet;
							state=ERROR_TRANSMIT;										
							if(Rx_Ecount>=ACTIVE_THRESHOLD)	error=PASSIVE;		//Set error states
						end		
						
		ERROR_TRANSMIT:	begin
							if(i<=Serial_count-DELIM_SIZE)			//Transmit error stream
							begin
								data<=Serial_stream[i];
								i<=i+1'b1;
							end
							else if(i>(Serial_count-DELIM_SIZE))		//wait until all error active nodes transmit Flag
							begin
								if(!bus.data) data<=`REC;
								else
								begin
									data<=Serial_stream[i];			//Then transmit error delimiter
									i<=i+1;
								end
							end
							state<=(i==Serial_count && bus.data)?BUS_RST:ERROR_TRANSMIT;	//Once done start fresh transaction after updating error counters
						end
						
		BUS_OFF:		begin state<=BUS_OFF;data<=`REC; end				//Bus off state
		 
		 endcase
	 end:no_reset
 end:generate procedural block
 
 //Checker procedural block - Performs Bit error,ACK error & Arbitration status by sampling CAN data line
 always_ff @(negedge clock)
 begin
 case(state)
						
 ARBITRATE:		begin
					if(bit_stuff)	CRC_array<=CRC_array;			//During arbitration,if bit-stuff high retain state
					else
					begin
						CRC_array[i-1]<=bus.data;						//Else keep sending sampled data to CRC_array as there is a possibility
						ARB_LOSS=(data==bus.data)?0:1;				//chance that the node might loose and become slave,so keep sampling 
																					//data even while arbitrating
						if(i==ARB_LENGTH+1 && !ARB_LOSS) state<=MASTER;			//Else if node won arbitration make it MASTER(no need to 
																						//continue  populating CRC_array)
				    else if(ARB_LOSS)																	
						begin
							state<=SLAVE;				//Else if arbitration lost i.e (sent bit!= sampled bit) node is slave 
							data<=`REC;
						end
					end 
				end

 MASTER:		begin				//During master mode check if data Tx is data seen on bus
					if(( (`DATA_PACKET) && (i!=DATA_ACK_SLOT) ) || ( (!`DATA_PACKET) && (i!=REQ_ACK_SLOT)) )
							BIT_ERROR=(data==bus.data)?0:1;			//If not bit error
					else if(( (`DATA_PACKET) && (i==DATA_ACK_SLOT) ) || ( (!`DATA_PACKET) && (i==REQ_ACK_SLOT)))
						begin
							ACK_ERROR=bus.data;				//During ACK Slot,check if line is dominant(signal from slaves that CRC_check 
																															//passed)
							{bitgen_en,bitchk_en}<=0;			//Else If bus is recessive then flag error
						end
				end
				
IFS:  			assert(bus.data)				//Assert Bus is low during IFS
				else state<=Tx_ERROR;				//Else flag error
						
						
SLAVE:			begin
					if(i<=CRC_Len && !bit_stuff && !CRC_CHK && !SLAVE_EOF)		//During slave mode, keep sampling payload data
						begin
							CRC_array[i]<=bus.data;
							if(i>ARB_LENGTH) CRC_Len=`RTR_BIT?REQ_CRC_LEN:DATA_CRC_LEN;		//Check to see if frame transmitted is Data or 
																											//Req and adjust your 
							i<=i+1'b1;																			//CRC length accordingly
						end
						
					else if(bit_stuff) 						//In case of a stuff signal preserve old values and ignore stuff bit on bus
						begin
							CRC_array<=CRC_array;
							CRC_chk<=CRC_chk;
						end
						
					else if(CRC_CHK)				//Once CRC array populated and Checker CRC generated,start comparing masters' CRC with 
																													//slaves'
						begin
							if(crc_count<=CRC_SIZE-1)
							begin
							  i<=0;
								assert (CRC_chk[crc_count]==bus.data) crc_count<=crc_count+1'b1;		//If mismatch flag error
								else state<=Rx_ERROR;
							end
							else
							begin					//Once checked all CRC bits of Master with Slave
								if(bus.data) 			//Check for CRC Delim i.e Bus should be recessive after the CRC data
								begin 
									CRC_CHK<=0; 
									SLAVE_ACK<=1'b1; 		//If Recessive,send ACK on line
								end
								else	state<=Rx_ERROR; 		//else flag CRC DELIM ERROR
							end:CRC_COUNT>CRC_SIZE
						end:CRC_CHK
						
					else if(SLAVE_EOF)			//Once successfully ACK'ed, wait for master to output EOF & IFS frames
					begin
						
						SLAVE_ACK<=0;
						count<=count+1'b1;
						if(count >=1 && !bus.data) state<=Rx_ERROR;			//If during this interval Bus goes dominant flag error
						if(count==(EOF_SIZE+BUS_IDLE_COUNT) && bus.data)
							begin
								if(!CRC_array[`RTR_BIT] && CRC_array[ID_SIZE:1]=={<<{Rx_ID}})  
								//Once transaction ends successfully,check your acceptance filter to see if you should accept the data, (all slaves ACK data but only the intended one ,i.e slave with acceptance filter configured, will store the received data)
								
									begin
											data_out_req<=1'b1;	
											{<<{Rx_packet}}<=CRC_array[(DATA_SIZE+DATA_START-1):DATA_START];	//If so store data and send it to XRTL transactor which maintains scoreboard of Tx & Rx packets
									end
								state<=BUS_RST;				//Get ready for next transaction
								if(Rx_Ecount>=ACTIVE_THRESHOLD)	Rx_Ecount<=ACTIVE_THRESHOLD-ERROR_STEP;		//Reset Rx error counters & 
																																	//states
								else	if (Rx_Ecount) 			Rx_Ecount<=Rx_Ecount-1'b1;					//after successful slave 
																															//transaction
							end:COUNT END
					
					end:SLAVE EOF
				end
					

endcase
end:Checker Block

//Task to pack Data packet
task automatic Data_Frame_Pack(ref Can_packet packet);
	{packet.Data.SOF,packet.Data.RTR,packet.Data.IDE,packet.Data.R0,packet.Data.CRC}<='0;
	{packet.Data.CRC_Delim,packet.Data.ACK,packet.Data.ACK_Delim,packet.Data.EOF}<='1;
	packet.Data.ID<={<<{Tx_ID}};packet.Data.Data<={<<{Tx_packet}};packet.Data.DLC<={<<{DLC}};
endtask
 
 //Task to pack Req packet
task automatic Req_Frame_Pack(ref Can_packet packet);
	{packet.Req.SOF,packet.Req.IDE,packet.Req.R0,packet.Req.CRC}<='0;
	{packet.Req.CRC_Delim,packet.Req.ACK,packet.Req.ACK_Delim,packet.Req.EOF,packet.Req.RTR}<='1;
	packet.Req.DLC<={<<{DLC}};packet.Req.ID<={<<{Rx_ID}};
endtask	
					
endmodule


