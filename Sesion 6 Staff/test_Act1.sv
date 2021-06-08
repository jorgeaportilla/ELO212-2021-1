`timescale 1ns / 1ps
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
module test_Act1();
//=============================================================
// Signal Definition
//=============================================================
    bit [3:0] registros;
    logic [8:0] Anodes;
    logic [6:0] Segments;
    logic [3:0] LEDs, flags_ref;
    bit [15:0] data_in, num_ref, num, out_num;
    bit reset, clk;
    int i;
    logic error_code = 'd0;
    logic pass;
    assign pass = ~(|(error_code));
    
//=============================================================
//  Clock  generator
//=============================================================
    always #1 clk = ~clk;
    
//=============================================================
//  Propertys & Sequences
//=============================================================   
    
	property displayed_num;
        @(posedge clk) disable iff (reset)
            ~$stable(num_ref) |-> ($past(num_ref) == out_num);
	endproperty
	
    property anodos;
        @(posedge clk) disable iff (reset) 
	    $onehot(~Anodes[3:0]); 
    endproperty 
	
	property flags_assert;
	   @(posedge clk) disable iff (reset)
	       flags_ref == LEDs;
	endproperty 
	
//=============================================================
//  Assertions Directive Layer
//=============================================================	
	
    assert property (flags_assert)
	else begin
		error_code = 'd001;
		$error("incorrect flags");
	end
	
    assert property(anodos)
    else begin 
	$error($sformatf("More than 1 display enabled: %04b", Anodes[3:0]));
        error_code = 3'b010;
    end
	
    assert property (displayed_num)
	else begin
		error_code = 'd011;
		$error("incorrect value in display");
	end
	
//=============================================================
//    Data Flow
//=============================================================
    initial begin
        reset = 'd1;
        registros = 'd1;
        #4
        reset = 1'b0;
        registros = 'd0;
        while(1) begin
            for(i =0 ; i <= 3; i++) begin
                #1 registros[i]= 'd1; 
                #1 registros[i]= 'd0;
            end
            #2;
        end
            
    end
    
    initial begin
		data_in = '0;
		#4
		while(1) begin
            @(posedge clk); data_in = $urandom();
		end
	end
	
//=============================================================
//    PASS or FAIL layer
//=============================================================
	
	initial begin 
	    forever begin
			#2
	       if( ~pass ) begin
            $display("------------------");
            if(pass) begin
                $display("       PASS       ");
            end 
            else begin
                $display("       FAIL       ");
            end
            
            $display("------------------");
            $finish;
            end
		end
	end
//=============================================================
//    Design Under Test
//=============================================================

    S6_actividad1#(16) DUT(
        .clk(clk), 
        .reset(reset),
        .load_A(registros[0]),
        .load_B(registros[1]),
        .load_Op(registros[2]),
        .updateRes(registros[3]),
        .data_in(data_in),
        
        .Segments(Segments),
	.Anodes(Anodes[3:0]),
        .LEDs(LEDs)
        
    );
    
//=============================================================
//    REFERENCE Module
//=============================================================
    
    ALU_reg_ref #(16) REFERENCE(
        .clk(clk), 
        .reset(reset),
        .load_A(registros[0]),
        .load_B(registros[1]),
        .load_Op(registros[2]),
        .updateRes(registros[3]),
        .data_in(data_in),

        .display(num_ref),
        .flags(flags_ref)
        
    );

//=============================================================
//    Decoder 7-segments to BCD
//=============================================================    
    sseg_decoder decoder (
        .clk(clk),
        .rst(reset),
        
        .dec(1'b0),
        .segments(Segments),
	    .anodes(Anodes[3:0]),
        
        .displayed_num(out_num)
    );

endmodule

