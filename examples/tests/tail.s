	.file	"tail.c"
	.text
	.p2align 4,,15
	.type	loop, @function
loop:
.LFB13:
	xorpd	%xmm8, %xmm8
	movlpd	8(%rsp), %xmm10
	movlpd	16(%rsp), %xmm9
	ucomisd	%xmm8, %xmm0
	jne	.L3
	jp	.L3
	ucomisd	%xmm8, %xmm1
	jne	.L5
	.p2align 4,,9
	jp	.L5
	ucomisd	%xmm8, %xmm2
	.p2align 4,,7
	jne	.L7
	.p2align 4,,9
	jp	.L7
	ucomisd	%xmm8, %xmm3
	.p2align 4,,7
	jne	.L9
	.p2align 4,,9
	jp	.L9
	ucomisd	%xmm8, %xmm4
	.p2align 4,,7
	jne	.L11
	.p2align 4,,9
	jp	.L11
	ucomisd	%xmm8, %xmm5
	.p2align 4,,7
	jne	.L13
	.p2align 4,,9
	jp	.L13
	ucomisd	%xmm8, %xmm6
	.p2align 4,,7
	jne	.L15
	.p2align 4,,9
	jp	.L15
	ucomisd	%xmm8, %xmm7
	.p2align 4,,7
	jne	.L17
	.p2align 4,,9
	jp	.L17
	ucomisd	%xmm8, %xmm10
	.p2align 4,,7
	jp	.L37
	.p2align 4,,9
	je	.L34
	.p2align 4,,9
	jmp	.L37
	.p2align 4,,7
.L40:
	.p2align 4,,11
	jp	.L17
	movlpd	-8(%rsp), %xmm7
	movq	%rdx, -8(%rsp)
	movlpd	-8(%rsp), %xmm9
.L34:
	ucomisd	%xmm8, %xmm9
	jp	.L38
	jne	.L38
	ucomisd	%xmm8, %xmm0
	jne	.L3
	.p2align 4,,9
	jp	.L3
	ucomisd	%xmm8, %xmm1
	.p2align 4,,7
	jne	.L5
	.p2align 4,,9
	jp	.L5
	ucomisd	%xmm8, %xmm2
	.p2align 4,,7
	jne	.L7
	.p2align 4,,9
	jp	.L7
	ucomisd	%xmm8, %xmm3
	.p2align 4,,7
	jne	.L9
	.p2align 4,,9
	jp	.L9
	ucomisd	%xmm8, %xmm4
	.p2align 4,,7
	jne	.L11
	.p2align 4,,9
	jp	.L11
	ucomisd	%xmm8, %xmm5
	.p2align 4,,7
	jne	.L13
	.p2align 4,,9
	jp	.L13
	ucomisd	%xmm8, %xmm6
	.p2align 4,,7
	jne	.L15
	.p2align 4,,9
	jp	.L15
	movsd	%xmm10, -8(%rsp)
	ucomisd	%xmm8, %xmm7
	movq	-8(%rsp), %rdx
	movsd	%xmm7, %xmm10
	movsd	%xmm6, -8(%rsp)
	movsd	%xmm5, %xmm6
	movsd	%xmm4, %xmm5
	movsd	%xmm3, %xmm4
	movsd	%xmm2, %xmm3
	movsd	%xmm1, %xmm2
	movsd	%xmm0, %xmm1
	movsd	%xmm9, %xmm0
	je	.L40
.L17:
	movsd	%xmm7, %xmm0
	ret
.L15:
	movsd	%xmm6, %xmm0
.L3:
	rep ; ret
.L37:
	movsd	%xmm10, %xmm0
	ret
.L5:
	movsd	%xmm1, %xmm0
	.p2align 4,,4
	ret
.L7:
	movsd	%xmm2, %xmm0
	.p2align 4,,4
	ret
.L9:
	movsd	%xmm3, %xmm0
	.p2align 4,,7
	ret
.L11:
	movsd	%xmm4, %xmm0
	.p2align 4,,7
	ret
.L13:
	movsd	%xmm5, %xmm0
	.p2align 4,,7
	ret
.L38:
	movsd	%xmm9, %xmm0
	.p2align 4,,7
	ret
.LFE13:
	.size	loop, .-loop
	.section	.rodata.str1.1,"aMS",@progbits,1
.LC1:
	.string	"%lf"
.LC3:
	.string	"%f\n"
	.section	.rodata.cst8,"aM",@progbits,8
	.align 8
.LC2:
	.long	0
	.long	0
	.text
	.p2align 4,,15
.globl main
	.type	main, @function
main:
.LFB14:
	movq	%rbx, -48(%rsp)
.LCFI0:
	movq	%rbp, -40(%rsp)
.LCFI1:
	movl	$.LC1, %edi
	movq	%r12, -32(%rsp)
.LCFI2:
	movq	%r13, -24(%rsp)
.LCFI3:
	xorl	%eax, %eax
	movq	%r14, -16(%rsp)
.LCFI4:
	movq	%r15, -8(%rsp)
.LCFI5:
	subq	$120, %rsp
.LCFI6:
	leaq	64(%rsp), %rbx
	movq	%rbx, %rsi
	call	scanf
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	movq	64(%rsp), %rbp
	call	scanf
	fldl	64(%rsp)
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	fstpl	24(%rsp)
	call	scanf
	fldl	64(%rsp)
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	fstpl	32(%rsp)
	call	scanf
	fldl	64(%rsp)
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	fstpl	40(%rsp)
	call	scanf
	fldl	64(%rsp)
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	fstpl	48(%rsp)
	call	scanf
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	movq	64(%rsp), %r15
	call	scanf
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	movq	64(%rsp), %r14
	call	scanf
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	xorl	%eax, %eax
	movq	64(%rsp), %r13
	call	scanf
	xorl	%eax, %eax
	movq	%rbx, %rsi
	movl	$.LC1, %edi
	movq	64(%rsp), %r12
	call	scanf
	movq	%rbp, 16(%rsp)
	movq	64(%rsp), %rax
	movlpd	16(%rsp), %xmm0
	ucomisd	.LC2(%rip), %xmm0
	je	.L45
.L42:
	movq	%rbp, 16(%rsp)
	movl	$.LC3, %edi
	movl	$1, %eax
	movlpd	16(%rsp), %xmm0
	call	printf
	movq	72(%rsp), %rbx
	movq	80(%rsp), %rbp
	movq	88(%rsp), %r12
	movq	96(%rsp), %r13
	movq	104(%rsp), %r14
	movq	112(%rsp), %r15
	addq	$120, %rsp
	ret
	.p2align 4,,7
.L45:
	jp	.L42
	movq	%r12, 16(%rsp)
	movlpd	48(%rsp), %xmm3
	movlpd	16(%rsp), %xmm7
	movq	%r13, 16(%rsp)
	movlpd	16(%rsp), %xmm6
	movq	%r14, 16(%rsp)
	movlpd	16(%rsp), %xmm5
	movq	%r15, 16(%rsp)
	movlpd	16(%rsp), %xmm4
	movq	%rbp, 8(%rsp)
	movlpd	40(%rsp), %xmm2
	movq	%rax, (%rsp)
	movlpd	32(%rsp), %xmm1
	movlpd	24(%rsp), %xmm0
	call	loop
	movsd	%xmm0, 16(%rsp)
	movq	16(%rsp), %rbp
	jmp	.L42
.LFE14:
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
	.long	.LFB13
	.long	.LFE13-.LFB13
	.uleb128 0x0
	.align 8
.LEFDE1:
.LSFDE3:
	.long	.LEFDE3-.LASFDE3
.LASFDE3:
	.long	.LASFDE3-.Lframe1
	.long	.LFB14
	.long	.LFE14-.LFB14
	.uleb128 0x0
	.byte	0x4
	.long	.LCFI6-.LFB14
	.byte	0xe
	.uleb128 0x80
	.byte	0x8f
	.uleb128 0x2
	.byte	0x8e
	.uleb128 0x3
	.byte	0x8d
	.uleb128 0x4
	.byte	0x8c
	.uleb128 0x5
	.byte	0x86
	.uleb128 0x6
	.byte	0x83
	.uleb128 0x7
	.align 8
.LEFDE3:
	.ident	"GCC: (GNU) 4.1.2 20061115 (prerelease) (Debian 4.1.1-21)"
	.section	.note.GNU-stack,"",@progbits
