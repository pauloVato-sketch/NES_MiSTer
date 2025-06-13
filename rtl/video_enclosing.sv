module video_enclosing
#(
	parameter LINE_LENGTH  = 768,
	parameter HALF_DEPTH   = 0,
	parameter GAMMA        = 0
)(
	// Inputs e outputs video.sv
    	input        clk,
	input        reset,
	input  [1:0] cnt,
	input  [5:0] color,
	input  [8:0] count_h,
	input  [8:0] count_v,
	input        hide_overscan,
	input  [3:0] palette,
	input  [2:0] emphasis,
	input  [1:0] reticle,
	input        pal_video,

	input        load_color,
	input [23:0] load_color_data,
	input  [5:0] load_color_index,

	output   wire hold_reset,

	/*output       ce_pix_OUT_VIDEO,
	output wire   HSync_OUT_VIDEO,
	output wire   VSync_OUT_VIDEO,
	output wire   HBlank_OUT_VIDEO,
	output wire   VBlank_OUT_VIDEO,
	output [7:0] R_OUT_VIDEO,
	output [7:0] G_OUT_VIDEO,
	output [7:0] B_OUT_VIDEO,*/

    	// Fim video.sv
    	// Inicio video_mixer.sv
    	input            CLK_VIDEO,
	output wire       CE_PIXEL,  // output pixel clock enable

	// input            ce_pix,    // input pixel clock or clock_enable

	input            scandoubler,
	input            hq2x, 	    // high quality 2x scaling

	inout     [21:0] gamma_bus,

	// color
	//input [DWIDTH:0] R_IN_MIXER,
	//input [DWIDTH:0] G_IN_MIXER,
	// input [DWIDTH:0] B_IN_MIXER,

	// Positive pulses.
	/*input            HSync_IN_MIXER,
	input            VSync_IN_MIXER,
	input            HBlank_IN_MIXER,
	input            VBlank_IN_MIXER,*/

	// Freeze engine
	// HDMI: displays last frame 
	// VGA:  black screen with HSync and VSync
	input            HDMI_FREEZE,
	output           wire freeze_sync,

	// video output signals
	output wire [7:0] VGA_R,
	output wire [7:0] VGA_G,
	output wire [7:0] VGA_B,
	output wire       VGA_VS,
	output wire       VGA_HS,
//	output wire       VGA_DE,

    	// inicio video_freak
	//input             CLK_VIDEO,
	// input             CE_PIXEL,
	// input             VGA_VS,
	input      [11:0] HDMI_WIDTH,
	input      [11:0] HDMI_HEIGHT,
	//input             VGA_DE_IN,
	
	//Video aspect ratio for VGA. 
	input      [11:0] ARX,
	input      [11:0] ARY,
	// 216 se crop ativado ou 0 caso contrário. 216p corrige problemas de tela
	// de consoles antigos que usavam 240p. Scaling inteiro de 5x (216 x 5 = 1080p).
	input      [11:0] CROP_SIZE,
	input       [4:0] CROP_OFF, // -16...+15
	input       [2:0] SCALE,     //0 - normal, 1 - V-integer, 2 - HV-Integer-, 3 - HV-Integer+, 4 - HV-Integer
	output            VGA_DE,
	
	//Video aspect ratio for HDMI. Most retro systems have ratio 4:3.
	output wire [12:0] VIDEO_ARX,
	output wire [12:0] VIDEO_ARY
);
localparam DWIDTH = HALF_DEPTH ? 3 : 7;
localparam DWIDTH_SD = GAMMA ? 7 : DWIDTH;
localparam HALF_DEPTH_SD = GAMMA ? 0 : HALF_DEPTH;

wire ce_pix;
wire HSync, VSync, HBlank, VBlank;
wire [7:0] R, G, B;
wire hold_reset;

video video
(
	// Inputs
	.clk(clk),
	.reset(reset),
	.cnt(cnt),
	.color(color),
	.count_v(count_v),
	.count_h(count_h),
	.hide_overscan(hide_overscan),
	.palette(palette),
	.load_color(load_color),
	.load_color_data(load_color_data),
	.load_color_index(load_color_index),
	.emphasis(emphasis),
	.reticle(reticle),
	.pal_video(pal_video),
	// Outputs
	.hold_reset(hold_reset),
	.ce_pix(ce_pix),
	.HSync(HSync),
	.VSync(VSync),
	.HBlank(HBlank),
	.VBlank(VBlank),
	.R(R),
	.G(G),
	.B(B)
);

// Wires for mixer:
// VGA_R, G, B, HS and VS and CE_PIXEL are wired to the output directly
// VGA_DE is the only output that only goes to video_freak and not back to emu.
wire VGA_DE_IN;
video_mixer #(260, 0, 1) video_mixer
(
	// Inputs
	.CLK_VIDEO(CLK_VIDEO), // (CLK_VIDEO)
	.ce_pix(ce_pix),
	.HDMI_FREEZE(HDMI_FREEZE),
	.freeze_sync(freeze_sync),
	.hq2x(hq2x),
	.gamma_bus(gamma_bus),
	.scandoubler(scandoubler),
	.R(R),
	.G(G),
	.B(B),
	.HSync(HSync),
	.VSync(VSync),
	.HBlank(HBlank),
	.VBlank(VBlank),
	// Outputs
	.CE_PIXEL(CE_PIXEL),
	.VGA_R(VGA_R),
	.VGA_G(VGA_G),
	.VGA_B(VGA_B),
	.VGA_VS(VGA_VS),
	.VGA_HS(VGA_HS),
	.VGA_DE(VGA_DE_IN)
);

video_freak video_freak
(
	// Inputs
	.CLK_VIDEO(CLK_VIDEO),
	.CE_PIXEL(CE_PIXEL),
	.VGA_VS(VGA_VS),
	.HDMI_WIDTH(HDMI_WIDTH),
	.HDMI_HEIGHT(HDMI_HEIGHT),
	.VGA_DE_IN(VGA_DE_IN),
	.ARX(ARX),
	.ARY(ARY),
	.CROP_SIZE(CROP_SIZE),
	.CROP_OFF(CROP_OFF),
	.SCALE(SCALE),
	// Outputs
	.VGA_DE(VGA_DE),
	.VIDEO_ARX(VIDEO_ARX),
	.VIDEO_ARY(VIDEO_ARY)
);



endmodule
