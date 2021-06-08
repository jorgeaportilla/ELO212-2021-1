`timescale 1ns / 1ps

/*
Universidad técnica Federico Santa María, Valparaíso
Autor: Patricio Henriquez
*/

module ALU_reg_ref#(
    parameter N = 16
) (

    input logic clk, reset, load_A, load_B, load_Op, updateRes,
    input logic [N-1 : 0] data_in,
    
    output logic [N-1:0] display,
    output logic [3:0] flags
);

    logic [N-1:0] A, B, Result_next, Result;
    logic [3:0] Status_next, Status;
    logic [1:0] OpCode;
    
    assign display = Result;
    
    always_ff @(posedge clk) begin 
        {A, B, OpCode, flags, Result} <= {A, B, OpCode, flags, Result};
        
        if(reset)
            {A, B, OpCode, flags, Result} <= 'd0;
        else begin
            if(updateRes)
                {flags, Result} <= {Status_next, Result_next}; 
            if(load_A)
                A <= data_in;
            if(load_B)
                B <= data_in;
            if(load_Op)
                OpCode <= data_in[1:0];
       end     
    end
    

    logic Neg, Z, C, V;
    
    always_comb begin
		case(OpCode)
			2'd0: begin
				{C, Result_next} = A + B;
				V = (Result_next[N-1] & ~A[N-1] & ~B[N-1]) | (~Result_next[N-1] & A[N-1] & B[N-1]);
			end

			2'd1: begin
				{C, Result_next} = A - B;
				V = (Result_next[N-1] & ~A[N-1] & B[N-1]) | (~Result_next[N-1] & A[N-1] & ~B[N-1]);
			end

			2'd2: begin
				Result_next = A | B;
				C = 1'b0;
				V = 1'b0;
			end

			2'd3: begin
				Result_next = A & B;
				C = 1'b0;
				V = 1'b0;
			end
		endcase

		Neg = Result_next[N-1];
		Z = (Result_next == '0);

		Status_next = {Neg, Z, C, V};
	end

endmodule
