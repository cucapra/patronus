module Delay(input clk);
    reg reg0 = 1'b0;
    reg reg1 = 1'b0;

    always @(posedge clk) begin
        // Set first register to 1,
        // Make second register copy
        reg0 <= 1'b1;
        reg1 <= reg0;
    end

    // Bad state: first register is 0 and second register is 1
    always @(*) begin
        assert (!((reg0 == 1'b0) && (reg1 == 1'b1)));
    end
endmodule
