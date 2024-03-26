	 /* 

Last update: 24/1/2024, 3:40PM
	Connected modules


*/

// parameters for instructions opcodes
parameter AND = 6'b000000;
parameter ADD = 6'b000001;
parameter SUB = 6'b000010;
parameter ANDI = 6'b000011;
parameter ADDI = 6'b000100;
parameter LW = 6'b000101;
parameter LW_POI = 6'b000110;
parameter SW = 6'b000111;
parameter BGT = 6'b001000;
parameter BLT = 6'b001001;
parameter BEQ = 6'b001010;
parameter BNE = 6'b001011;
parameter JMP = 6'b001100;
parameter CALL = 6'b001101;
parameter RET = 6'b001110;
parameter PUSH = 6'b001111;
parameter POP = 6'b010000;

parameter IF = 3'b000;
parameter ID = 3'b001;
parameter EX = 3'b010;
parameter MEM = 3'b011;
parameter WB = 3'b100;



parameter sp_index =  4'b1111; // stack pointer index in register file (R15)

/*
	Module:
		ALU
		
	Inputs:
		alu_op: operation to execute in ALU
		data1: first operand input
		data2: second data operand
	
	Outputs:
		alu_res: result operation on data1 and data2
		C, N, V, Z: flags after the operation
		
	
	Last Modified:
		10/1/2024 10:40PM
*/

module ALU(
	input [1:0] alu_op,
	input [31:0] data1,
	input [31:0] data2,
	output reg [31:0] alu_res,
	output reg C, 
    output wire N, V, Z // negative, overflow, and zero - flags
	);

	
	always @(*) begin 
		case (alu_op)
			2'b00:  {C, alu_res} = data1 + data2;
			2'b01:  {C, alu_res} = data1 - data2;
			2'b10:  {C, alu_res} = data1 & data2;
		endcase
	end
	
	assign  Z = ~(|alu_res); // Zero flag
	assign  V = (alu_res[31] ^ C); // Overflow flag
	assign  N = alu_res[31]; // Negative flag
	
	
endmodule	




module alu_tb;
  // Signals
  reg [1:0] alu_op;
  reg [31:0] a, b;
  reg [2:0] op;
  wire [31:0] out;
  wire C, N, V, Z;

  // Instantiate ALU module
  ALU uut (
    .alu_op(alu_op),
    .data1(a),
    .data2(b),
    .alu_res(out),
    .C(C),
    .N(N),
    .V(V),
    .Z(Z)
  );
  initial begin
    a = 32'h0000000A; // 10 in hexadecimal
    b = 32'h00000005; // 5 in hexadecimal
    alu_op = 2'b00; // Addition
    #10;
    $display("a = %h, b = %h, operation = %h, out = %h, C = %b, N = %b, V = %b, Z = %b", a, b, alu_op, out, C, N, V, Z);

    alu_op = 2'b01; // Subtraction
    #10;
    $display("a = %h, b = %h, operation = %h, out = %h, C = %b, N = %b, V = %b, Z = %b", a, b, alu_op, out, C, N, V, Z);

    a = 32'h00001112;
    b = 32'h00000004;
    alu_op = 2'b10; // AND
    #10;
    $display("a = %h, b = %h, operation = %h, out = %h, C = %b, N = %b, V = %b, Z = %b", a, b, alu_op, out, C, N, V, Z);
    $finish;
  end
endmodule


//##############################################################################################################################


/*
	Module:
		instruction memory
	
	Inputs:
		address: memory address to read instruction from that address (the address is obtained from PC register)
	
	Outputs:
		inst: the instruction we read
		

	Last Modified:
		11/1/2024 1:20 AM
*/

  

//#############################################################################################################################	

/*
	Module:
		Register File	
	
	Inputs:
		clk: the clock
		RA_address: the register address to read on busA or write on it the data on busW2 for LW.POI and POP (RS1 or SP)
		RB_address: the register address to read on busB (RS2 or RD)								   
		RW_address: register address to read on that register the data on busW2
		busW1: the input data for writing (if needed)
		busW2: second input data for writing (if needed)
		reg_write1: indicates whether we want to write on register RW the data on busW1
		reg_write2: indicates whether we want to write on register RA the data on busW2
		
	Outputs:
		busA: the data read from RA register
		busB: the data read from RB register
	
	Last modified:
		11/1/2024 2:00AM
	
*/		



module register_file( 
	input clk, 
	input [3:0] RA_address,
	input [3:0] RB_address,
	input [3:0] RW_address,
	input [31:0] busW1,
	input [31:0] busW2,
	output reg [31:0] busA, 
	output reg [31:0] busB,
	input reg_write1,
	input reg_write2
	);
	
	reg [31:0] regs [15:0];	
	
	// in the last code that connects the modules, there we write the code that decides what are RA_address and RB_address. 
	   
	always @(negedge clk) begin 
		
	   	 busB <= regs[RB_address];
	   	 busA <= regs[RA_address];	 	
	end
	
	always @(posedge clk) begin 	 
		
 		if (reg_write1) begin
			 regs[RW_address] <= busW1;
		end
		   
	   	if (reg_write2 ) begin
			 regs[RA_address] <= busW2;
		end
		
	end
	
	
	initial begin	
		
        regs[0] <= 32'h00000000;
        regs[1] <= 32'h00000001;
        regs[2] <= 32'h00000002;
        regs[3] <= 32'h00000003;
        regs[4] <= 32'h00000004;
        regs[5] <= 32'h00000005;
        regs[6] <= 32'h00000006;
        regs[7] <= 32'h00000007;
        regs[8] <= 32'h00000008;
        regs[9] <= 32'h00000009;
        regs[10] <= 32'h0000000A;
		regs[11] <= 32'h0000000B;
		regs[12] <= 32'h0000000C;
		regs[13] <= 32'h0000000D;
		regs[14] <= 32'h0000000E;
		regs[15] <= data_mem_size ;
    end

endmodule	   
 
`timescale 1ns / 1ps  


module register_file_tb;

    // Inputs
    reg clk;
    reg [3:0] RA_address;
    reg [3:0] RB_address;
    reg [3:0] RW_address;
    reg [31:0] busW1;
    reg [31:0] busW2;
    reg reg_write1;
    reg reg_write2;

    // Outputs
    wire [31:0] busA;
    wire [31:0] busB;

    // Instantiate the Unit Under Test (UUT)
    register_file uut (
        .clk(clk), 
        .RA_address(RA_address), 
        .RB_address(RB_address), 
        .RW_address(RW_address), 
        .busW1(busW1), 
        .busW2(busW2), 
        .busA(busA), 
        .busB(busB), 
        .reg_write1(reg_write1), 
        .reg_write2(reg_write2)
    );

    // Clock generation
    always #10 clk = ~clk;

    // Test procedure
    initial begin
        // Initialize Inputs
        clk = 0;
        RA_address = 0;
        RB_address = 0;
        RW_address = 0;
        busW1 = 0;
        busW2 = 0;
        reg_write1 = 0;
        reg_write2 = 0;

        // Wait 100 ns for global reset to finish
        #50;

        // Add stimulus here
        // Example: Writing to a register and reading from it
        reg_write1 = 1;
        RW_address = 4;
        busW1 = 32'hA5A5A5A5;
        #20;
        reg_write1 = 0;
        RA_address = 4;
        #20;

        // Example: Testing simultaneous write and read
        reg_write2 = 1;
        RW_address = 5;
        RA_address = 5;
        busW2 = 32'h5A5A5A5A;
        #20;
        reg_write2 = 1;
		reg_write1 = 1;	
		RA_address=4; // Reg[RA-address] <-- busW2
		RW_address = 4;//Reg[RW_address	] <--- busW1 [This done on the first]
	    // the last value ob Reg[4] should be the value of the BusW2
		busW1=31'haaaabbbb	;	
		busW2=31'h66667777	 ;
		 #20  ;
        #20;				
        // Add more test cases as needed

        $finish;
    end
      
endmodule

//######################################################################################################################################

parameter data_mem_size = 1024 ; // size of the data memory (in words)


/*
	Module:
		Data Memory	
	
	Inputs:
		clk: the clock
		address: the address to read from, goes to data_out
		mem_write: indicates whether we want to write on memory
		mem_read: indicates whether we want to read from memory
		
	Outputs:										  
		data_out: the data we read from memory
	
	Last modified:
		11/1/2024 2:15AM
	
*/


module Data_mem (	
	input clk,
	input [31:0] address, 
	input [31:0] data_in, 
	output reg [31:0] data_out,
	input mem_read, // signal for reading from memory
	input mem_write // signal for writing on memory
	);			  
	
	
	reg [31:0] mem[0:data_mem_size - 1];
	
	always @(posedge clk ) begin
		
		if (mem_write) 
		   mem[address] <= data_in;
		
		else if (mem_read)	
		   data_out <= mem[address];
		
	end
			
	initial begin
		
		// initialize the memory with temporary value.
	    for (int i = 0; i < 1024; i = i + 1) begin
	      mem[i] = i;
	    end
	
	end
	

endmodule	   

`timescale 1ns / 1ps

module Data_mem_tb;

    // Inputs
    reg clk;
    reg [31:0] address;
    reg [31:0] data_in;
    reg mem_read;
    reg mem_write;

    // Outputs
    wire [31:0] data_out;

    // Instantiate the Unit Under Test (UUT)
    Data_mem uut (
        .clk(clk),
        .address(address),
        .data_in(data_in),
        .data_out(data_out),
        .mem_read(mem_read),
        .mem_write(mem_write)
    );

    // Clock generation
    always #10 clk = ~clk;

    // Test procedure
    initial begin
        // Initialize Inputs
        clk = 0;
        address = 0;
        data_in = 0;
        mem_read = 0;
        mem_write = 0;

        // Wait for global reset
        #50

        // Test Case 1: Write to Memory
        address = 10;
        data_in = 32'h12345678;
        mem_write = 1;
		mem_read=0;	 
		
        #50; 
		mem_write = 0;
		mem_read=1;
       
        #20;

        // Test Case 2: Read from Memory
        mem_read = 1;
        #20;
        #20;

        $finish;
    end
      
endmodule


//#######################################################################################################################	 



/*
	Module:
		Control Unit	
	
	Inputs:
		Z, V, C, N: falgs from ALU
		opcode: the instruciton opcode
		
	Outputs:										  
		all signals, including pc source selection, memory, register file, and mux'es selection lines.
	
	Last modified:
		29/1/2024 6:00PM
	
*/

module control_unit(   
	input Z, V, C, N, // flags, needed for Branch conditions (for PC source signal)
	input [5:0] opcode,
	output reg sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, sel_wb_data, reg_write1, reg_write2, extend_op, mem_Din, sel_BusW2,
	output reg [1:0] sel_address_mem, pc_src, alu_op
	);
											// conditions for LT and GT are swapped here, since it's RD (>/</==) RS1 (we do RS1 - RD,..)   
	reg branch_taken;
	assign  branch_taken = (opcode == BEQ && Z) || (opcode == BNE && !Z) || (opcode == BLT && !Z && N == V) || (opcode == BGT && N != V);	
	assign  sel_RA = (opcode == CALL || opcode == RET || opcode == PUSH || opcode == POP);
	assign  sel_RB = ~(opcode == AND || opcode == ADD || opcode == SUB);
	assign  sel_alu_operand = (opcode == ANDI || opcode == ADDI || opcode == LW || opcode == LW_POI || opcode == SW);
	assign  sel_address_mem = ( (opcode == RET || opcode == POP) ? 2 : ( opcode == CALL || opcode == PUSH) ? 1 : 0 );
	assign  read_mem = (opcode == LW || opcode == LW_POI || opcode == POP || opcode == RET);
	assign  write_mem = (opcode == SW || opcode == CALL || opcode == PUSH);
	assign  sel_wb_data = (opcode == LW || opcode == LW_POI || opcode == POP);
	assign  reg_write1 = (opcode == ADD || opcode == AND || opcode == SUB || opcode == ANDI || opcode == ADDI || opcode == LW || opcode == LW_POI || opcode == POP); 
	assign  reg_write2 = (opcode == LW_POI || opcode == POP || opcode == PUSH || opcode == RET || opcode == CALL);
	assign  extend_op = (opcode != ANDI);
	assign  mem_Din = (opcode == CALL);
	assign  pc_src = (opcode == JMP || opcode == CALL) ? 1 : 
                (opcode == RET) ? 3 : 
                (branch_taken) ? 2 : 0;

	assign  alu_op = ((opcode == AND || opcode == ANDI ) ? 2 : (opcode == SUB || opcode == BEQ || opcode == BLT || opcode == BGT || opcode == BNE) ? 1 : 0);	
	assign sel_BusW2 = (opcode == PUSH || opcode == CALL) ? 1 : 0;
                //  (opcode == LW_POI || opcode == POP || opcode == RET) ? 0 : 0;

endmodule

`timescale 1ns / 1ps

module control_unit_tb;

    // Inputs
    reg Z, V, C, N;
    reg [5:0] opcode;

    // Outputs
    wire sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, sel_wb_data, reg_write1, reg_write2, extend_op, mem_Din, sel_BusW2;
    wire [1:0] sel_address_mem, pc_src, alu_op;

    // Instantiate the Unit Under Test (UUT)
    control_unit control ( 
	
        .Z(Z), 
        .V(V), 
        .C(C), 
        .N(N), 
        .opcode(opcode), 
        .sel_RA(sel_RA), 
        .sel_RB(sel_RB), 
        .sel_alu_operand(sel_alu_operand), 
        .read_mem(read_mem), 
        .write_mem(write_mem), 
        .sel_wb_data(sel_wb_data), 
        .reg_write1(reg_write1), 
        .reg_write2(reg_write2), 
        .extend_op(extend_op), 
        .mem_Din(mem_Din),
        .sel_address_mem(sel_address_mem),
        .pc_src(pc_src), 
        .alu_op(alu_op),		 
		.sel_BusW2(sel_BusW2)
    );

    initial begin
        // Initialize Inputs
        Z = 1;
        V = 1;
        C = 0;
        N = 0;
	   #10;
        opcode = 6'b010000; // Replace with actual opcode
        #10; // Wait for 10ns

        // Display outputs
       $display("Time = %d : opcode = %b, sel_RA = %b, sel_RB = %b, sel_alu_operand=%b, ", 
	   $time, opcode, sel_RA, sel_RB, sel_alu_operand);		 
	   $display("---------------------------------------------------------------------------");
       $display("read_mem = %b, write_mem = %b, sel_wb_data = %b, reg_write1 = %b, ", 
	   read_mem, write_mem, sel_wb_data, reg_write1);	
	   $display("---------------------------------------------------------------------------");
       $display("reg_write2 = %b, extend_op = %b, mem_Din = %b, pc_src = %d, sel_ = %d, sel_BusW2 =%b", 
         reg_write2, extend_op, mem_Din, pc_src, sel_address_mem, sel_BusW2);

        #100;
        $finish;
    end

endmodule




// ############################################################/



/*
	Module:
		Extender
	
	Inputs:
		extend_op: if 0 then extend with 0, else extend with sign bit.
		A: 16-bit immediate value to extend it to 32 bits.
	Outputs:										  
		B: the extended output (Extended-A).
	
	Last modified:
		11/1/2024 2:00AM
	
*/
module extender(
	input [15:0] A,
	output reg [31:0] B,
	input extend_op
	);
	
	
	always @(*) begin 
	   
		if (extend_op == 0)
			 B <= {16'b0, A[15:0]}; // unsigned immediate (extend with zeros)
		else 
			 B <= {{16{A[15]}}, A[15:0]}; // signed extend (extend with MSB in A)
			
	end
	

endmodule	   
`timescale 1ns / 1ps

module extender_tb;

    // Inputs
    reg [15:0] A;
    reg extend_op;

    // Outputs
    wire [31:0] B;

    // Instantiate the Unit Under Test (UUT)
    extender uut (
        .A(A), 
        .B(B), 
        .extend_op(extend_op)
    );

    // Test procedure
    initial begin
        // Initialize Inputs
        A = 0;
        extend_op = 0;

        // Wait 100 ns for global reset to finish
        #10;

        // Add stimulus here
        // Test Case 1: Zero Extension
        A = 16'h1234;
        extend_op = 0; // Zero extension
        #20;

        
        // Test Case 3: Sign Extension with negative value
        A = 16'hF234; // MSB is 1, indicating a negative value
        extend_op = 1; // Sign extension
        #20;

        // Add more test cases as needed

        $finish;
    end
      
endmodule
////////////////////////////////////////////////////////////////////////


/*
	Module:
		Instruction Memory	
	
	Inputs:
		clk: the clock
		address: the address to read from, goes to the IR
	
		
	Outputs:										  
		inst: the instruciton register (IR)
	
	Last modified:
		11/1/2024 2:00AM
	
*/

module Inst_mem(
	input [31:0] address,
	output reg [31:0] inst
	);
	
	parameter MEM_SIZE = 1024;
    parameter WORD_SIZE = 32;
	
	reg [WORD_SIZE-1:0] mem [0:MEM_SIZE-1];
	
	initial begin	
				
		
		mem[0] = 32'b00111110010000000000000000000000;	      		  // PUSH R9 (Push the value of R9 on the top of the stack)
		mem[1] = 32'b01000000000000000000000000000000;	     	     // POP R0 (Pop the value on top of the stack to register R0)
		mem[2] = 32'b00000100010000001000000000000000;      	    // ADD R1, R0, R2 
		//mem[3] = 32'h0D44001B; 					      	       // andi $5,$1,6	   (I-Type)	
		//mem[3] = 32'b00110100000000000000000000000111;  	 	  // CALL 26'b00000000000000000000000111 (7) goes to instruction 7
		//mem[3] = 32'b00110000000000000000000000000111; 			 // JMP 0x07 
		mem[3] = 32'b00011101010001000000000001000011;    		// SW R5,R1,16  (unused mode bits 11)	mem[R5+16] <= R9  
		mem[4] = 32'b00010101100011000000000001100011;         // LW R6, R3, 0x018 (R6 = Mem(R3 + 0x18)		
		mem[5] = 32'b00011001100011000000000001100011;  	  // LW.POI R6, R3, 0x018 (R6 = Mem(R3 + 0x18), R3 = R3+1).
		/*
		mem[7] = 32'b00111110010000000000000000000000;	      		  // PUSH R9 (Push the value of R9 on the top of the stack)
		mem[8] = 32'b01000000000000000000000000000000;	     	     // POP R0 (Pop the value on top of the stack to register R0)
		mem[9] = 32'b00000100010000001000000000000000;      	    // ADD R1, R0, R2 
		mem[10] = 32'b00111000000000000000000000000000;			 // RET (returns to PC on top of the stack.
		*/
		
		//mem[7] = 32'b00010000100010000000000000000100;        // ADDI R2, R2, 0x01		  								
		
		
		//mem[8] = 32'b00100001000010111111111111111100; 		 // BGT R4, R2, -1 // go to instruction (PC - 1) above instruction	
		
		//mem[7] = 32'b00011001110010000000000001100001; // LW.POI R7, R2, 0x18
		/* 	    32'b000111 10010101000000000001000011 		
		
		mem[0] = 32'b00111110010000000000000000000000;	  // PUSH R9 (Push the value of R9 on the top of the stack) 
		mem[1] = 32'b01000000000000000000000000000000;	 // POP R0 (Pop the value on top of the stack to register R0)
		mem[2] = 32'b00000100010000001000000000000000;  // ADD R1, R0, R2
		mem[3] = 32'h19C40021;  					   // LW.POI R7,R1,8	(Load mem(R1 + sign_extend(8)) to R7)
		mem[4] = 32'h158C0010; 						  // LW R6,R3,4
		mem[5] = 32'h090C8000;   				     // sub R4,R3,R2
		mem[6] = 32'h0D44001B; 						// andi $5,$1,6	   (I-Type)
		mem[7] = 32'h1E540043; 					   //SW $9,$5,16  (unused mode bits 11)	mem[R5+16] <= 9
	  
	    mem[9] = 32'h34000004; 					 // CALL 4 (Pushes PC+1 to the top of the stack and next_pc = {pc[31:26], sign_extend(4))
		mem[9] = 32'h38000000; 				// RET	(return PC to the value stored on top of the stack)
		mem[10] = 32'h33FFFFFD; 					  // JMP -3 (constant represented in 2's complement)	
		*/
	
	end

	
	always @(address) begin
		inst <= mem[address];
	end		  
	
endmodule

module instruction_memory_tb;
    reg [31:0] addr; 
    wire [31:0] data_out;

    Inst_mem mem(addr, data_out);

    initial begin		 
        addr = 0;
        #20;
        $display("Instruction = %h", data_out);
        #10;	
		addr = 1;
        #10;
        $display("Instruction = %h", data_out);
        #10; 
		addr = 2;
        #10;
        $display("Instruction = %h", data_out);
        #10;
		addr = 3;
        #10;
        $display("Instruction = %h", data_out);
        #10;
		addr = 4;
        #10;
        $display("Instruction = %h", data_out);
        #10;
		addr = 5;
        #10;
        $display("Instruction = %h", data_out);
        #10;
        $finish;
    end
endmodule

//############################################################################################################################


/*
	Module:
		CPU, the last module that connects everything together
	
	Inputs:
		clk: the clock
		reset: the reset signal to initialize
		
		
	Outputs:										  
		inputs and outputs of inner modules are defined as outputs to see them in the waveform diagram.
		current_state: the current stage in the execution of the current instruciton.

	Last modified:
		11/1/2024 2:00AM
	
*/


module CPU (
    input clk,
    input reset, 
	output reg[31:0] pc,
	output reg [31:0] ir,
	output reg sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, reg_write1,reg_write2,sel_wb_data ,mem_Din, sel_BusW2,
	output reg [1:0] alu_op,sel_address_mem	,
    output reg [31:0] busA, // first operand output
    output reg [31:0] busB, // second operand output
	output reg [3:0] RA,
	output reg [3:0] RB,
	output reg [2:0] current_state,
	output reg [31:0] alu_res, busW1 , busW2 ,data_out,
	output reg [3:0] RD, RS1, RS2,
	output reg [31:0] alu_operand1, alu_operand2,
	output reg [31:0] address,
	output reg [31:0] data_in,
	output reg [1:0] pc_src, 
	output reg [31:0] BTA, // branch target address (for B-type instructions (BGT, BLT, BEQ, BNE)) 
	output reg N, V, Z,  // negative, overflow, and zero - flags (assigned in ALU module using assign statements)
	output reg C // carry flag (defined in ALU module inside an always block, so we need to declare it as a reg here)
); 
	
	
reg [2:0] next_state;
 

reg [15:0] A;
reg [31:0] B;

reg [1:0] mode; // for LW.POI and SW instructions
reg [5:0] opcode;

reg [31:0] jump_target; // for J-type instructions (JMP, CALL)





reg [31:0] RW;	 
reg extend_op;

Inst_mem inst_mem1(pc, ir);
register_file register_file1(clk, RA, RB, RW, busW1, busW2, busA, busB, reg_write1, reg_write2);
ALU alu1(alu_op, alu_operand1, alu_operand2, alu_res, C, N, V, Z);
control_unit control_unit1(Z, V, C, N, opcode, sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, sel_wb_data, reg_write1, reg_write2, extend_op, mem_Din, sel_BusW2, sel_address_mem, pc_src, alu_op);
Data_mem data_mem1(clk, address, data_in, data_out, read_mem, write_mem);
extender extender1(A, B, extend_op);


always @(posedge clk or negedge reset) begin
    if (!reset) begin
        next_state <= IF; 
        pc <= 32'h00000000; // initialize program counter to zero	
        alu_operand1 <= 0; 
        alu_operand2 <= 0; 
        busW1 <= 0;
        busW2 <= 5;
        address <= 0;
        data_in <= 0;
   		current_state <= 0;
    end
	
    else begin 	
		
    
        current_state = next_state;

        case (current_state)

            IF: begin  	 
			  
				#20
                case (pc_src)
                    0: pc = pc + 1; 
                    1: pc = jump_target;
                    2: pc = BTA;
                    3: pc = data_out; // for RET instruction (return to the address on the top of the stack)   
                endcase
				
			//	pc <= next_pc;
            end

            ID: begin
				
			   #20
                opcode <= ir[31:26];
				 
                RD <= ir[25:22]; 
                RS1 <= ir[21:18];
                RS2 <= ir[17:14];
			  	RW <= ir[25:22];
                A <= ir [18: 2]; // for I-type instructions (ANDI, ADDI, LW, LW.POI)
				#5
                mode <= ir[1:0]; // for LW.POI and SW instructions
                jump_target <= {pc[31:26], ir[25:0]}; // for J-type instructions (JMP, CALL)
                BTA <= pc + B;
				
			   #5
			   if (sel_RA == 0)
                    RA <= RS1;
                else if (sel_RA == 1)
                    RA <= sp_index;
                #5
                if (sel_RB == 0)
                    RB <= RS2;
                else if (sel_RB == 1)
                    RB <= RD; 
							 	
            end 

            EX: begin
				#10
                alu_operand1 <= busA;  
				
				#10
                if (sel_alu_operand == 0)
                    alu_operand2 <= busB;
                else if (sel_alu_operand == 1)
                    alu_operand2 <= B;	
			 	
				
				            
            end
            MEM: begin 
				
				//busW2 <= busA;
			
			   #5
			   if (sel_address_mem == 0)
                    address <= alu_res;
                else if (sel_address_mem == 1)
                    address <= busA - 1; // for PUSH, CALL (first decrement SP, then write on it)
                else if (sel_address_mem == 2)
                    address <= busA; // for POP, RET (first read from SP, then increment it by in write back stage)
				
				#5
				if (mem_Din == 0)
					data_in <= busB;
				else
					data_in <= pc+1; // for return
				
			
            end 
            WB: begin 
				
				#5
                if (sel_wb_data == 0)
                    busW1 = alu_res;
                else if (sel_wb_data == 1)
                    busW1 = data_out;	
				   
				#5
				if (sel_BusW2 == 0 && reg_write2)  // LW.POI and POP
                    busW2 = busA + 1;
                else if (sel_BusW2 == 1 && reg_write2)	// for PUSH operation (push and call)
                    busW2 = busA - 1; 	
	
            end

        endcase 
    end
	
	


    case (current_state)
        IF: begin
            next_state = ID;
			//pc <= next_pc;
        end
        ID: begin
            
            if (opcode == JMP)
                next_state = IF;
            else if (opcode >= AND && opcode <= BNE)
                next_state = EX; 
			else if (opcode >= CALL && opcode <= POP)
				next_state = MEM;

        end
        EX: begin
            
            if (opcode >= BGT && opcode <= BNE)
                next_state = IF;
            else if (opcode >= AND && opcode <= ADDI)
                next_state = WB; 
            else if (opcode >= LW && opcode <= SW)
                next_state = MEM;
        end
        MEM: begin
            if (opcode == SW)
                next_state = IF;
            else if ((opcode >= CALL && opcode <= POP) || opcode == LW ||  opcode == LW_POI )
                next_state = WB;
        end
        WB: begin
            next_state = IF; // always go back to IF stage after WB stage
        end
    endcase
end	 


// When busA changes, busW2 changes as well, since busW2 in the datapath depends on busA (see WB stage in the above always block). 
always @(busA) begin

	busW2 <= busA;
end


endmodule 	

module CPU_tb;

    reg clk;
    reg reset;
    // Define signals to capture CPU outputs
    wire [31:0] pc;
    wire [31:0] ir;	
	wire [2:0] current_state;
    wire sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, reg_write1, reg_write2, sel_wb_data, mem_Din, sel_BusW2;
    wire [1:0] alu_op;
    wire [31:0] busA, busB, alu_res, busW1, busW2, data_out;
    wire [3:0] RA, RB;
    wire [3:0] RD, RS1, RS2;
	wire [31:0] alu_operand1, alu_operand2;		
	wire [31:0] address;
	wire [31:0] data_in;
	wire N, V, Z, C;  
	wire [1:0] pc_src;
	wire [31:0] BTA;
	
  // Instantiate the CPU module
    CPU dut(
        .clk(clk),
        .reset(reset),
        .pc(pc),
        .ir(ir),
        .sel_RA(sel_RA),
        .sel_RB(sel_RB),
        .sel_alu_operand(sel_alu_operand),
        .read_mem(read_mem),
        .write_mem(write_mem),
        .reg_write1(reg_write1),
        .reg_write2(reg_write2),
        .sel_wb_data(sel_wb_data),
        .mem_Din(mem_Din),
        .sel_BusW2(sel_BusW2),
        .alu_op(alu_op),
        .sel_address_mem(sel_address_mem),
        .busA(busA),
        .busB(busB),
        .RA(RA),
        .RB(RB),
        .alu_res(alu_res),
        .busW1(busW1),
        .busW2(busW2),
        .data_out(data_out),
		.address(address),
		.alu_operand1(alu_operand1),
		.alu_operand2(alu_operand2),
        .RD(RD),
        .RS1(RS1),
        .RS2(RS2),
		.data_in(data_in),
		.current_state(current_state), // to print
		.N(N),
		.C(C),
		.V(V),
		.Z(Z),
		.pc_src(pc_src),
		.BTA(BTA)
    );

  // Clock generation
  always #50 clk = ~clk;

  // Initial block
  initial begin
    // Initialize inputs
    clk = 1;
    reset = 1; // Keep reset high initially
    
    // un-reset
    #1 reset = 0; 
	
	#1 reset = 1;

    
    // You can apply inputs and check the outputs based on your requirements

    // Observe initial state
  // #50

   
    // Observe the state after a few clock cycles
    //#500;
$display("___________________________________________________________________________");  


$display("After Clock Cycles - IF: ");
        $display("pc = %h", pc);
        $display("ir = %h", ir);
        $display("sel_RA = %b", sel_RA);
        $display("sel_RB = %b", sel_RB);
        $display("sel_alu_operand = %b", sel_alu_operand);
        $display("read_mem = %b", read_mem);
        $display("write_mem = %b", write_mem);
        $display("reg_write1 = %b", reg_write1);
        $display("reg_write2 = %b", reg_write2);
        $display("sel_wb_data = %b", sel_wb_data);
        $display("mem_Din = %h", mem_Din);
        $display("sel_BusW2 = %b", sel_BusW2);
        $display("alu_op = %b", alu_op);
        $display("sel_address_mem = %b", sel_address_mem);
        $display("busA = %h", busA);
        $display("busB = %h", busB);
        $display("RA = %h", RA);
        $display("RB = %h", RB);
        $display("alu_res = %h", alu_res);
        $display("busW1 = %h", busW1);
        $display("busW2 = %h", busW2);
        $display("RD = %h", RD);
        $display("RS1 = %h", RS1);
        $display("RS2 = %h", RS2);
		$display("alu_operand1 = %d", alu_operand1);
		$display("alu_operand2 = %d", alu_operand2); 
		$display("mem_address = %h", address);
		$display("data_out = %h", data_out);
		$display("data_in = %h", data_in);
    // Add more test cases as needed

    #9922 $finish; // Finish simulation after some time
  end

endmodule

