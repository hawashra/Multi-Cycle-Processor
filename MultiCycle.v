	 /* 

Last update: 12/1/2024, 3:40PM

	shereen

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
	output reg C, N, V, Z // carry, negative, overflow, and zero - flags
	);

	
	always @(*) begin 
		case (alu_op)
			2'b00: {C, alu_res} = data1 + data2;
			2'b01: {C, alu_res} = data1 - data2;
			2'b10: {C, alu_res} = data1 & data2;
		endcase
	end
	
	
	assign Z = ~(|alu_res); // Zero flag
	assign V = (alu_res[31] ^ C); // Overflow flag
	assign N = alu_res[31]; // Negative flag

	
	
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



module Inst_mem(
	input [31:0] address,
	output reg [31:0] inst
	);
	
	parameter MEM_SIZE = 1024;
    parameter WORD_SIZE = 32;
	
	reg [WORD_SIZE-1:0] mem [0:MEM_SIZE-1];
	
	initial begin	
				
	  mem[0] = 32'h090C8000;   //sub $4,$3,$2	  (R-Type)
	  mem[1] = 32'h0D44001B; //	 andi $5,$1,6	   (I-Type)
	  mem[2] = 32'h158C0010; //LW $6,$3,4		   (I-Type with mode = 00)
	  mem[3] = 32'h15C00061;  //LW.POI $7,$1,8	 (mode = 01)
	  mem[4] = 32'h1E540043; //SW $9,$5,16  (unused mode bits 11)
	  mem[5] = 32'h33FFFFFD; // JMP -3 (constant represented in 2' complement)
	  mem[6] = 32'h34000004; // CALL 4	  
	  mem[7] = 32'h38000000; // RET	
	  mem[8]=  32'h3D800000; //PUSH $6
	  mem[9] = 32'h40800000; // POP $2
	end
	
	
	always @(address) begin
		inst = mem[address];
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
	
	always @(posedge clk) begin 
		
		if (reg_write1) begin
			regs[RW_address] <= busW1;
		end
		
		if (reg_write2) begin
			regs[RA_address] = busW2;
		end					 
		 
			
	   busA <= regs[RA_address];	 
	   busB <= regs[RB_address];
	end
	    initial begin
        regs[0] = 32'h00000000;
        regs[1] = 32'h00000001;
        regs[2] = 32'h00000002;
        regs[3] = 32'h00000003;
        regs[4] = 32'h00000004;
        regs[5] = 32'h00000005;
        regs[6] = 32'h00000006;
        regs[7] = 32'h00000007;
        regs[8] = 32'h00000008;
        regs[9] = 32'h00000009;
        regs[10] = 32'h0000000A;
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


module Data_mem (	
	input clk,
	input [31:0] address, 
	input [31:0] data_in, 
	output reg [31:0] data_out,
	input mem_read, // signal for reading from memory
	input mem_write // signal for writing on memory
	);			  
	
	
	reg [31:0] mem[0:1023];
	
	
	always @(posedge clk ) begin
		
		if (mem_write) 
		  mem[address] = data_in;
		
		else if (mem_read)	
			data_out = mem[address];
			
	end
			
	initial begin
		
		// initialize the memory with temporary value.
	    for (int i = 0; i < 256; i = i + 1) begin
	      mem[i] <= 32'hAAAAAAAA;
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


	// will complete documentation later, bored for now.

	Last Modified:
		12/1/2024 1:00AM
*/

module control_unit(   
	input Z, V, C, N, // flags, needed for Branch conditions (for PC source signal)
	input [5:0] opcode,
	output reg sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, write_back_data, reg_write1, reg_write2, extend_op, mem_Din, sel_BusW2,
	output reg [1:0] address_mem, pc_src, alu_op
	);
	
	reg branch_taken;
	assign  branch_taken = (opcode == BEQ && Z) || (opcode == BNE && !Z) || (opcode == BLT && N != V) || (opcode == BGT && !Z && N == V);	
	assign sel_RA = (opcode == CALL || opcode == RET || opcode == PUSH || opcode == POP);
	assign sel_RB = ~(opcode == AND || opcode == ADD || opcode == SUB);
	assign sel_alu_operand = (opcode == ANDI || opcode == ADDI || opcode == LW || opcode == LW_POI || opcode == SW);
	assign address_mem = ( (opcode == RET || opcode == POP) ? 2 : ( opcode == CALL || opcode == PUSH) ? 1 : 0 );
	assign read_mem = (opcode == LW || opcode == LW_POI || opcode == POP || opcode == RET);
	assign write_mem = (opcode == SW || opcode == CALL || opcode == PUSH);
	assign write_back_data = (opcode == LW || opcode == LW_POI || opcode == POP);
	assign reg_write1 = (opcode == ADD || opcode == AND || opcode == SUB || opcode == ANDI || opcode == ADDI || opcode == LW || opcode == LW_POI || opcode == POP); 
	assign reg_write2 = (opcode == LW_POI || opcode == POP);
	assign extend_op = (opcode != ANDI);
	assign mem_Din = (opcode == CALL);
	assign pc_src = (opcode == JMP || opcode == CALL) ? 1 : 
                (opcode == RET) ? 3 : 
                (branch_taken) ? 2 : 0;

	assign alu_op = ((opcode == AND) ? 2 : (opcode == SUB || opcode == BEQ || opcode == BLT || opcode == BGT || opcode == BNE) ? 1 : 0);	
	assign sel_BusW2 = (opcode == PUSH || opcode == CALL) ? 1 :
                  (opcode == LW_POI || opcode == POP || opcode == RET) ? 0 : 0;

	


endmodule

`timescale 1ns / 1ps

module control_unit_tb;

    // Inputs
    reg Z, V, C, N;
    reg [5:0] opcode;

    // Outputs
    wire sel_RA, sel_RB, sel_alu_operand, read_mem, write_mem, write_back_data, reg_write1, reg_write2, extend_op, mem_Din, sel_BusW2;
    wire [1:0] address_mem, pc_src, alu_op;

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
        .write_back_data(write_back_data), 
        .reg_write1(reg_write1), 
        .reg_write2(reg_write2), 
        .extend_op(extend_op), 
        .mem_Din(mem_Din),
        .address_mem(address_mem), 
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
       $display("read_mem = %b, write_mem = %b, write_back_data = %b, reg_write1 = %b, ", 
	   read_mem, write_mem, write_back_data, reg_write1);	
	   $display("---------------------------------------------------------------------------");
       $display("reg_write2 = %b, extend_op = %b, mem_Din = %b, pc_src = %d, address_mem = %d, sel_BusW2 =%b", 
         reg_write2, extend_op, mem_Din, pc_src, address_mem, sel_BusW2);

        #100;
        $finish;
    end

endmodule




	// ############################################################/
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




//############################################################################################################################