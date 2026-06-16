module Swap(input clk);
    reg a = 1'b0;
    reg b = 1'b1;

    always @(posedge clk) begin
        // Swap register values
        a <= b;
        b <= a;
    end

    // Bad state: register values are the same
    always @(*) begin
        assert (a != b);
    end
endmodule