	.file	"sum12.c"
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC0:
	.string	"%lf"
.LC1:
	.string	"%f\n"
	.text
	.p2align 4,,15
.globl main
	.type	main, @function
main:
.LFB94:
	subq	$24, %rsp
.LCFI0:
	movl	$.LC0, %edi
	xorl	%eax, %eax
	leaq	16(%rsp), %rsi
	call	scanf
	movlpd	16(%rsp), %xmm0
	movl	$.LC1, %edi
	movl	$1, %eax
	addsd	%xmm0, %xmm0
	call	printf
	addq	$24, %rsp
	ret
.LFE94:
	.size	main, .-main
	.section	.eh_frame,"a",@progbits
.Lframe1:
	.long	.LECIE1-.LSCIE1
.LSCIE1:
	.long	0x0
	.byte	0x1
	.string	"zR"
	.uleb128 0x1
	.sleb128 -8
	.byte	0x10
	.uleb128 0x1
	.byte	0x3
	.byte	0xc
	.uleb128 0x7
	.uleb128 0x8
	.byte	0x90
	.uleb128 0x1
	.align 8
.LECIE1:
.LSFDE1:
	.long	.LEFDE1-.LASFDE1
.LASFDE1:
	.long	.LASFDE1-.Lframe1
	.long	.LFB94
	.long	.LFE94-.LFB94
	.uleb128 0x0
	.byte	0x4
	.long	.LCFI0-.LFB94
	.byte	0xe
	.uleb128 0x20
	.align 8
.LEFDE1:
	.ident	"GCC: (GNU) 4.1.2 20061115 (prerelease) (Debian 4.1.1-21)"
	.section	.note.GNU-stack,"",@progbits
