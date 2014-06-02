all: puresim

VLOG = \
	hdl/top.sv \
	hdl/can.sv	\
	hdl/bitstuff.sv	\
	hdl/can_bus.sv	\
	hdl/Monitor.sv
	
SVLOG = \
	hvl/can_hvl.sv

puresim:
	vlib puresim_work
	vmap work puresim_work 
	vlog -f $(TBX_HOME)/questa/hdl/xtlm_files.f
	vlog $(SVLOG)
	vlog $(VLOG)
	tbxsvlink -puresim
	
veloce:
	vlib tbx_work
	vmap work tbx_work
	vlog -f $(TBX_HOME)/questa/hdl/xtlm_files.f
	vlog $(SVLOG)
	tbxcomp -top top $(VLOG) -veloce
	tbxsvlink -veloce


