
//
//DESCRIPTION: CAN Bus Interface. Has a single wire-AND line
// 0 is Dominant state and 1 is recessive state on bus

`include "def.pkg"
interface can_bus(input [Total_Nodes-1:0] input_data);

wire data = (1'b1 & (&input_data));

//Error handle function for CAN node
function automatic void Error_Handle(const ref errorstate_t ERROR,ref int error_count,ref Error_Frame Error_packet);
error_count=error_count+8;
Error_packet.Delim='1;
if(ERROR==ACTIVE) Error_packet.Flag='0;
if(ERROR==PASSIVE)	 Error_packet.Flag='1;
endfunction

//CRC generator - code re-used from Bosch's CAN specification
function automatic void CRC_gen(const ref logic [DATA_CRC_LEN:0] CRC_array,ref int CRC_Len,output logic [CRC_SIZE-1:0] CRC_RG);
  automatic logic CRCNXT=0;
  parameter N_CRC=15;
  CRC_Len=`RTR_BIT?REQ_CRC_LEN:DATA_CRC_LEN;
  for(int i=0;i<=CRC_Len;i++)
  begin
  CRCNXT=CRC_array[i] ^ CRC_RG[N_CRC-1];
  CRC_RG<<=1;
  if(CRCNXT)
  CRC_RG=CRC_RG ^ CRC_Poly;
  end
  CRC_RG={<<{CRC_RG}};
endfunction
endinterface
