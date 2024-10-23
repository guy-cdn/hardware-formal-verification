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
// In many (older) serial communications protocols, each data byte is sent
// along with a start bit and a stop bit, to help the receiver delimit bytes
// from the stream of bits. One common scheme is to use one start bit (0), 8
// data bits, and 1 stop bit (1). The line is also at logic 1 when nothing
// is being transmitted (idle). Design a finite state machine that will
// identify when bytes have been correctly received when given a stream of
// bits. It needs to identify the start bit, wait for all 8 data bits, then
// verify that the stop bit was correct. The module will also output the
// correctly- received data byte. out_byte needs to be valid when done is 1,
// and is don't-care otherwise.If the stop bit does not appear when
// expected, the FSM must wait until it finds a stop bit before attempting
// to receive the next byte. Include a active-high synchronous reset. Note
// that the serial protocol sends the least significant bit first. It should
// assert done each time it finds a stop bit.
// 
// module TopModule (
//   input clk,
//   input in,
//   input reset,
//   output [7:0] out_byte,
//   output done
// );

module RefModule (
  input clk,
  input in,
  input reset,
  output [7:0] out_byte,
  output done
);

  parameter B0=0, B1=1, B2=2, B3=3, B4=4, B5=5, B6=6, B7=7, START=8, STOP=9, DONE=10, ERR=11;
  reg [3:0] state;
  reg [3:0] next;

  reg [9:0] byte_r;

  always_comb begin
    case (state)
      START: next = in ? START : B0;  // start bit is 0
      B0: next = B1;
      B1: next = B2;
      B2: next = B3;
      B3: next = B4;
      B4: next = B5;
      B5: next = B6;
      B6: next = B7;
      B7: next = STOP;
      STOP: next = in ? DONE : ERR;  // stop bit is 1. Idle state is 1.
      DONE: next = in ? START : B0;
      ERR: next = in ? START : ERR;
    endcase
  end

  always @(posedge clk) begin
    if (reset) state <= START;
      else state <= next;
  end

  always @(posedge clk) begin
    byte_r <= {in, byte_r[9:1]};
  end

  assign done = (state==DONE);
  assign out_byte = done ? byte_r[8:1] : 8'hx;

endmodule
