project( fraud-alert )
cmake_minimum_required( VERSION 2.6 )
#set ( CMAKE_BUILD_TYPE Debug )
set ( CMAKE_BUILD_TYPE Release )
add_definitions ( -Wall -std=c++11 )

#-----------------------------------------------------------
# BOOST support configured
#-----------------------------------------------------------
FIND_PACKAGE( Boost COMPONENTS system iostreams filesystem graph REQUIRED )
INCLUDE_DIRECTORIES( ${Boost_INCLUDE_DIRS} )

add_executable(fraud-alert-bfs src/fraud-alert-bfs.cpp)
target_link_libraries ( fraud-alert-bfs
    ${Boost_LIBRARIES}
    rt
     )

add_executable(fraud-alert src/fraud-alert.cpp)
target_link_libraries ( fraud-alert
    ${Boost_LIBRARIES}
    rt
     )