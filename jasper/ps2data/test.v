// MIT License
// 
// Copyright (c) 2023-2024 NVIDIA Research Projects
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
// SOFTWARE.
// 
// 
// This project contains code from human-eval (https://github.com/openai/human-eval/).
// 
// The MIT License
// 
// Copyright (c) OpenAI (https://openai.com)
// 
// Permission is hereby granted, free of charge, to any person obtaining a copy
// of this software and associated documentation files (the "Software"), to deal
// in the Software without restriction, including without limitation the rights
// to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
// copies of the Software, and to permit persons to whom the Software is
// furnished to do so, subject to the following conditions:
// 
// The above copyright notice and this permission notice shall be included in
// all copies or substantial portions of the Software.
// 
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
// FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
// AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
// LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
// OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
// THE SOFTWARE.
 
// The following module was created using AI, using the following prompt, which
// provides the spec.  See https://github.com/NVlabs/verilog-eval/ for details.

// Prompot / spec:
//
// We want a finite state machine that will search for message boundaries
// when given an input byte stream. The algorithm we'll use is to discard
// bytes until we see one with in[3]=1. We then assume that this is byte 1
// of a message, and signal the receipt of a message once all 3 bytes have
// been received (done). The FSM should signal done in the cycle immediately
// after the third byte of each message was successfully received.
// 
// Implement the datapath module that will output the 24-bit (3 byte)
// message whenever a packet is received (out_bytes[23:16] is the first
// byte, out_bytes[15:8] is the second byte, etc.). The reset signal is
// active high synchronous. out_bytes needs to be valid whenever the done
// signal is asserted. You may output anything at other times (i.e.,
// don't-care).
// 
//   Waveform example:
//   time   clk rst in  done out_bytes
//   0ns    0   1    0  x         x
//   5ns    1   1    0  0         x
//   10ns   0   1    0  0         x
//   15ns   1   0   2c  0         x
//   20ns   0   0   2c  0         x
//   25ns   1   0   81  0         x
//   30ns   0   0   81  0         x
//   35ns   1   0    9  0         x
//   40ns   0   0    9  0         x
//   45ns   1   0   6b  1    2c8109
//   50ns   0   0   6b  1    2c8109
//   55ns   1   0    d  0         x
//   60ns   0   0    d  0         x
//   65ns   1   0   8d  0         x
//   70ns   0   0   8d  0         x
//   75ns   1   0   6d  1    6b0d8d
//   80ns   0   0   6d  1    6b0d8d
//   85ns   1   0   12  0         x
//   90ns   0   0   12  0         x
//   95ns   1   0    1  0         x
//   100ns  0   0    1  0         x
//   105ns  1   0    d  1    6d1201
//   110ns  0   0    d  1    6d1201
//   115ns  1   0   76  0         x
//   120ns  0   0   76  0         x
//   125ns  1   0   3d  0         x
//   130ns  0   0   3d  0         x
//   135ns  1   0   ed  1     d763d
//   140ns  0   0   ed  1     d763d
//   145ns  1   0   8c  0         x
//   150ns  0   0   8c  0         x
//   155ns  1   0   f9  0         x
//   160ns  0   0   f9  0         x
//   165ns  1   0   ce  1    ed8cf9
//   170ns  0   0   ce  1    ed8cf9
//   175ns  1   0   c5  0         x
//   180ns  0   0   c5  0         x
//   185ns  1   0   aa  0         x
//   190ns  0   0   aa  0         x
//  
// module TopModule (
//   input clk,
//   input [7:0] in,
//   input reset,
//   output [23:0] out_bytes,
//   output done
// );

module ps2data (
  input clk,
  input [7:0] in,
  input reset,
  output [23:0] out_bytes,
  output done
);

  parameter BYTE1=0, BYTE2=1, BYTE3=2, DONE=3;
  reg [1:0] state;
  reg [1:0] next;

  wire in3 = in[3];

  always_comb begin
    case (state)
      BYTE1: next = in3 ? BYTE2 : BYTE1;
      BYTE2: next = BYTE3;
      BYTE3: next = DONE;
      DONE: next = in3 ? BYTE2 : BYTE1;
    endcase
  end

  always @(posedge clk) begin
    if (reset) state <= BYTE1;
      else state <= next;
  end

  assign done = (state==DONE);

  reg [23:0] out_bytes_r;
  always @(posedge clk)
    out_bytes_r <= {out_bytes_r[15:0], in};

  // Implementations may vary: Allow user to do anything while the output
  // doesn't have to be valid.

  assign out_bytes = done ? out_bytes_r : 'x;

  // Assertions checking the free-language spec:
  done_valid_ast:        assert property (@(posedge clk) done |-> $past(in[3], 3) == 1);
  out_bytes_0_valid_ast: assert property (@(posedge clk) done |-> out_bytes[7:0]   == $past(in, 1));
  out_bytes_1_valid_ast: assert property (@(posedge clk) done |-> out_bytes[15:8]  == $past(in, 2));
  out_bytes_2_valid_ast: assert property (@(posedge clk) done |-> out_bytes[23:16] == $past(in, 3));

endmodule
