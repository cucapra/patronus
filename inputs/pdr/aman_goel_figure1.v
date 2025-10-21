`define W 16
module example(clk);
  input clk;
  reg [`W-1:0] u = `W'd1;
  reg [`W-1:0] v = `W'd1;
  always @(posedge clk) begin
    if (u < v) u <= u + v;
    else u <= v + `W'd1;
    v <= v + `W'd1;
  end

  always @(*) assert ((u + v) != `W'd1);
endmodule
