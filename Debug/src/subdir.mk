################################################################################
# Automatically-generated file. Do not edit!
################################################################################

# Add inputs and outputs from these tool invocations to the build variables 
C_SRCS += \
../src/dice.c \
../src/graph.c \
../src/hikerdice_branch_and_bound.c 

OBJS += \
./src/dice.o \
./src/graph.o \
./src/hikerdice_branch_and_bound.o 

C_DEPS += \
./src/dice.d \
./src/graph.d \
./src/hikerdice_branch_and_bound.d 


# Each subdirectory must supply rules for building sources it contributes
src/%.o: ../src/%.c
	@echo 'Building file: $<'
	@echo 'Invoking: GCC C Compiler'
	gcc -std=c99 -O0 -g3 -Wall -c -fmessage-length=0 -MMD -MP -MF"$(@:%.o=%.d)" -MT"$(@)" -o "$@" "$<"
	@echo 'Finished building: $<'
	@echo ' '


