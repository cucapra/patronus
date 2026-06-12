module Overflow(input clk);
    reg [1:0] count = 2'h2;

    always @(posedge clk) begin
        count <= count + 2'h1;
    end

    always @(*) begin
        assert (count != 2'h0);
    end
endmodule