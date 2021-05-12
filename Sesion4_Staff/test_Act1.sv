//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++
//   DUT With assertions
//+++++++++++++++++++++++++++++++++++++++++++++++++++++++++++++

`timescale 1ns / 1ps

module test_Act1();

//=============================================================
// Signal Definition
//=============================================================

	logic [31:0]   in_num, out_num;
	logic [3:0]    out_digits [0:7];
	logic [6:0]    out_segs;
	logic [7:0]    out_an;
	logic [2:0]    error_code = 3'b000;
	logic pass;
	assign pass = ~(|(error_code));

//=============================================================
//  Clock & Reset generator
//=============================================================

	bit clk = 1'b0;
	bit rst = 1'b1;

	always #1 clk = ~clk;
	always_ff @(posedge clk) rst <= 1'b0;

//=============================================================
//  Propertys & Sequences
//=============================================================

	
    property anodos;
        @(posedge clk) disable iff (rst) 
        	$onehot(~out_an); 
    endproperty 
    
    property display_num;
        @(posedge clk) disable iff (rst)  
        	~$stable(out_num) |-> (out_num == $past(in_num));
    endproperty 

//=============================================================
//  Assertions Directive Layer
//=============================================================
   
    assert property(display_num)
    else begin 
        $error($sformatf("Displaying %08X, but expected %08X", out_num, in_num));
        error_code = 3'b001;
    end
	
    assert property(anodos)
    else begin 
        $error($sformatf("More than 1 display enabled: %08b", out_an));
        error_code = 3'b010;
    end
    
//=============================================================
//    Data Flow
//=============================================================

    initial begin 
        in_num = 'd0;
        repeat(1) @(posedge clk);       //dejo un canto libre por el reset
        
        while(1) begin
			repeat(8) @(posedge clk);   //cada 8 cantos ingreso un nuevo valor
			in_num = $urandom;
		end
    end 
    
//=============================================================
//    Decoder 7-segments to BCD
//=============================================================

    initial begin
		out_num = 32'd0;

		repeat(1) @(posedge clk);  //canto libre por reset

		repeat(100000) begin
			out_digits = {4'bX, 4'bX, 4'bX, 4'bX, 4'bX, 4'bX, 4'bX, 4'bX};

			repeat(8) begin	@(posedge clk); 

				for(int i = 0; i < 8; ++i) begin
					if(out_an[i]) continue;

					case(out_segs)
						7'b0000001: out_digits[i] = 4'h0;

						7'b1001111: out_digits[i] = 4'h1;

						7'b0010010: out_digits[i] = 4'h2;

						7'b0000110: out_digits[i] = 4'h3;

						7'b1001100: out_digits[i] = 4'h4;

						7'b0100100: out_digits[i] = 4'h5;

						7'b0100000: out_digits[i] = 4'h6;

						7'b0001111: out_digits[i] = 4'h7;
						7'b0001101: out_digits[i] = 4'h7;
						7'b0001110: out_digits[i] = 4'h7;

						7'b0000000: out_digits[i] = 4'h8;

						7'b0001100: out_digits[i] = 4'h9;
						7'b0000100: out_digits[i] = 4'h9;

						7'b0001000: out_digits[i] = 4'hA;
						7'b0000010: out_digits[i] = 4'hA;

						7'b1100000: out_digits[i] = 4'hB;

						7'b0110001: out_digits[i] = 4'hC;
						7'b1110010: out_digits[i] = 4'hC;

						7'b1000010: out_digits[i] = 4'hD;

						7'b0110000: out_digits[i] = 4'hE;
						7'b0010000: out_digits[i] = 4'hE;

						7'b0111000: out_digits[i] = 4'hF;
					endcase
				end
			end
			
			out_num = {out_digits[7], out_digits[6], out_digits[5], out_digits[4],
			           out_digits[3], out_digits[2], out_digits[1], out_digits[0]};
			
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


	S4_actividad1 DUT
	(
		.clock(clk),
		.reset(rst),

		.BCD_in(in_num),

		.segments(out_segs),
		.anodos(out_an)
	);
		
		
//=============================================================
endmodule