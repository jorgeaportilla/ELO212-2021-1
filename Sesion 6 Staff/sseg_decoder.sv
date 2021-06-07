module sseg_decoder #(parameter C_SWAP_SEGMENTS = 1)
(
	input logic clk,
	input logic rst,

	input logic dec,
	input logic [6:0] segments,
	input logic [3:0] anodes,

	output logic [15:0] displayed_num
);
	logic [3:0] digits[0:3];

	always_ff @(posedge clk) begin
		if(rst)
			displayed_num <= 'd0; 
		else 
			displayed_num <= {digits[3], digits[2], digits[1], digits[0]};	
	end

	for(genvar i = 0; i < 4; ++i) begin
		always_ff @(posedge clk) begin
			if(rst) begin
				digits[i] <= 4'h0;
			end 
			else if(~anodes[i]) begin
				case(segments)
					7'b0000001: digits[i] <= 4'h0;

					7'b1001111: digits[i] <= 4'h1;

					7'b0010010: digits[i] <= 4'h2;

					7'b0000110: digits[i] <= 4'h3;

					7'b1001100: digits[i] <= 4'h4;

					7'b0100100: digits[i] <= 4'h5;

					7'b0100000: digits[i] <= 4'h6;

					7'b0001111: digits[i] <= 4'h7;
					7'b0001101: digits[i] <= 4'h7;
					7'b0001110: digits[i] <= 4'h7;

					7'b0000000: digits[i] <= 4'h8;

					7'b0001100: digits[i] <= 4'h9;
					7'b0000100: digits[i] <= 4'h9;

					7'b0001000: digits[i] <= 4'hA;
					7'b0000010: digits[i] <= 4'hA;

					7'b1100000: digits[i] <= 4'hB;

					7'b0110001: digits[i] <= 4'hC;
					7'b1110010: digits[i] <= 4'hC;

					7'b1000010: digits[i] <= 4'hD;

					7'b0110000: digits[i] <= 4'hE;
					7'b0010000: digits[i] <= 4'hE;

					7'b0111000: digits[i] <= 4'hF;

					default: digits[i] <= 'X;
				endcase
			end
		end
	end
endmodule