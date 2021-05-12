`timescale 1ns / 1ps

//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

module test_Act3();

//=============================================================
//  Clock generator
//=============================================================

	bit clk = 1'b1;
	always #1 clk = ~clk;
	
//=============================================================
// Signal Definition
//=============================================================

	logic [7:0] A, B, Result, ResultRef;
	logic [3:0] Status, StatusRef;
	logic [1:0] OpCode;
	logic [2:0] error_code = 'd0;
	logic finish;
	assign finish = &{A, B, Result};
	logic pass;
	assign pass = ~(|(error_code));

	

//=============================================================
//  if-else property
//=============================================================
    
    property error_result;
        @(posedge clk) 
        if(OpCode == 'd0 | OpCode == 'd1)
            Result == ResultRef
        else 
            Result == ResultRef;
    endproperty 
	
	property error_flags;
		@(posedge clk) 
        if(OpCode == 'd0 | OpCode == 'd1)
            Status == StatusRef
        else 
            Status[2] == StatusRef[2];
	
	endproperty


//=============================================================
//    Data Flow
//============================================================= 
    
	initial begin
		{A, B, OpCode} = '0;
		
		while(1) begin
			@(posedge clk); {A, B, OpCode} += 'd1;
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
            if( pass ) begin
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
//  Assertions Directive Layer
//=============================================================
    
    assert property (error_result)
    else begin 
        $error($sformatf("A: %02X | B: %02X | Op: %d | Output is %02X, but expected %02X ", 
               A, B, OpCode, Result, ResultRef));
        error_code = 3'b001;
    end
	
	assert property(error_flags)
	else begin 
		$error($sformatf("Status: %04b, but expected Status: %04b", Status, StatusRef));
		error_code = 3'b010;
	end
	

	
//=============================================================
//    Instance Modules
//=============================================================


	S4_actividad3 #(8) DUT
	(
		.A(A),
		.B(B),

		.OpCode(OpCode),

		.Result(Result),
		.Status(Status)
	);

//=============================================================
//    Instance Reference Module
//=============================================================
	

	ALU_ref #(8) REF
	(
		.A(A),
		.B(B),

		.OpCode(OpCode),

		.Result(ResultRef),
		.Status(StatusRef)
	);
	
	
//=============================================================	
endmodule