`timescale 1ns / 1ps
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
module test_Act2();

//=============================================================
// Signal Definition
//=============================================================
    logic [63:0] count, load_value = (2**63) - 1;
    logic dec, enable, reset, load, reset_tb;
    logic [2:0] error_code = 'd0; 
    logic finish;
    int time_press;
    assign finish = &{load, enable, dec};
	logic pass;
	assign pass = ~(|(error_code));

//=============================================================
//  Clock & Reset generator
//=============================================================
    bit clk;
    always #1 clk = ~clk;

//=============================================================
//  Propertys & Sequences
//=============================================================

    property dec_assert;
        @(negedge clk) disable iff (reset_tb) 
        if(load)
            $stable(count) |-> count == load_value
        else if(enable) 
            if(dec)
                $stable(count) |-> $past(count) == count + 'd1
            else 
                $stable(count) |->  $past(count) == count - 'd1
        else 
            (~enable & ~load) |-> $past(count) == count;
    endproperty 

//=============================================================
//  Assertions Directive Layer
//=============================================================

    assert property (dec_assert)
    else begin 
        $error("El contador no está bien definido");
        error_code = 3'b001;
    end
    
//=============================================================
//  Tasks & Functions Layer
//=============================================================    


//=============================================================
//    Data Flow
//=============================================================
    
    initial begin 
        reset = 1'b1;
        reset_tb = 1'b1;
        {load, enable, dec} = 3'b000;      
        #3
        reset = 1'b0;
        #1
        reset_tb = 1'b0; 

        while(1) begin
            time_press = $urandom_range(200,600);
			#time_press {load, enable, dec} += 'd1;
		end  
    end

//=============================================================
//    PASS or FAIL layer
//=============================================================
	
	initial begin
	   forever begin 
	       #2
	       if(finish | ~pass) begin
            $display("------------------");
            if(pass) begin
                $display("       PASS       ");
            end else begin
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
    S4_actividad2 #(
        .N(64)
    )DUT(
        .clock(clk),
        .reset(reset),
        .load(load),
        .dec(dec),
        .load_value(load_value),
        .enable(enable),
        .counterN(count)
    );

//=============================================================  

endmodule
