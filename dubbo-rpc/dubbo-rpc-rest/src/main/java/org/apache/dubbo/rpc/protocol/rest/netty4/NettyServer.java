package org.apache.dubbo.rpc.protocol.rest.netty4;

import org.apache.dubbo.common.URL;
import org.apache.dubbo.common.config.ConfigurationUtils;
import org.apache.dubbo.common.logger.ErrorTypeAwareLogger;
import org.apache.dubbo.common.logger.LoggerFactory;
import org.apache.dubbo.common.utils.NetUtils;
import org.apache.dubbo.remoting.Constants;
import org.apache.dubbo.remoting.transport.netty4.NettyEventLoopFactory;
import org.apache.dubbo.remoting.transport.netty4.ssl.SslServerTlsHandler;

import io.netty.bootstrap.ServerBootstrap;
import io.netty.buffer.PooledByteBufAllocator;
import io.netty.channel.ChannelFuture;
import io.netty.channel.ChannelInitializer;
import io.netty.channel.ChannelOption;
import io.netty.channel.EventLoopGroup;
import io.netty.channel.socket.SocketChannel;
import io.netty.handler.codec.http.HttpObjectAggregator;
import io.netty.handler.codec.http.HttpServerCodec;
import io.netty.util.concurrent.Future;

import java.net.InetSocketAddress;

import static java.util.concurrent.TimeUnit.MILLISECONDS;
import static org.apache.dubbo.common.constants.CommonConstants.ANYHOST_KEY;
import static org.apache.dubbo.common.constants.CommonConstants.ANYHOST_VALUE;
import static org.apache.dubbo.common.constants.CommonConstants.IO_THREADS_KEY;
import static org.apache.dubbo.common.constants.CommonConstants.KEEP_ALIVE_KEY;
import static org.apache.dubbo.common.constants.CommonConstants.SSL_ENABLED_KEY;
import static org.apache.dubbo.common.constants.LoggerCodeConstants.TRANSPORT_FAILED_CLOSE;
import static org.apache.dubbo.remoting.Constants.EVENT_LOOP_BOSS_POOL_NAME;
import static org.apache.dubbo.remoting.Constants.EVENT_LOOP_WORKER_POOL_NAME;

public class NettyServer {
    private static final ErrorTypeAwareLogger logger = LoggerFactory.getErrorTypeAwareLogger(NettyServer.class);


    /**
     * netty server bootstrap.
     */
    private ServerBootstrap bootstrap;
    /**
     * the boss channel that receive connections and dispatch these to worker channel.
     */
    private io.netty.channel.Channel channel;

    private final URL url;

    private final InetSocketAddress bindAddress;
    private EventLoopGroup bossGroup;
    private EventLoopGroup workerGroup;
    private final int serverShutdownTimeoutMills;

    private final RestResolver restResolver;

    public NettyServer(URL url, RestResolver restResolver) {
        String bindIp = url.getParameter(Constants.BIND_IP_KEY, url.getHost());
        int bindPort = url.getParameter(Constants.BIND_PORT_KEY, url.getPort());
        if (url.getParameter(ANYHOST_KEY, false) || NetUtils.isInvalidLocalHost(bindIp)) {
            bindIp = ANYHOST_VALUE;
        }
        bindAddress = new InetSocketAddress(bindIp, bindPort);

        // read config before destroy
        serverShutdownTimeoutMills = ConfigurationUtils.getServerShutdownTimeout(url.getOrDefaultModuleModel());
        this.url = url;
        this.restResolver = restResolver;
        open();
    }

    private void open() {
        bootstrap = new ServerBootstrap();

        bossGroup = createBossGroup();
        workerGroup = createWorkerGroup();

        initServerBootstrap();

        // bind
        ChannelFuture channelFuture = bootstrap.bind(bindAddress);
        channelFuture.syncUninterruptibly();
        channel = channelFuture.channel();

    }

    protected EventLoopGroup createBossGroup() {
        return NettyEventLoopFactory.eventLoopGroup(1, EVENT_LOOP_BOSS_POOL_NAME);
    }

    protected EventLoopGroup createWorkerGroup() {
        return NettyEventLoopFactory.eventLoopGroup(
            url.getPositiveParameter(IO_THREADS_KEY, Constants.DEFAULT_IO_THREADS),
            EVENT_LOOP_WORKER_POOL_NAME);
    }

    protected void initServerBootstrap() {
        boolean keepalive = url.getParameter(KEEP_ALIVE_KEY, Boolean.FALSE);

        bootstrap.group(bossGroup, workerGroup)
            .channel(NettyEventLoopFactory.serverSocketChannelClass())
            .option(ChannelOption.SO_REUSEADDR, Boolean.TRUE)
            .childOption(ChannelOption.TCP_NODELAY, Boolean.TRUE)
            .childOption(ChannelOption.SO_KEEPALIVE, keepalive)
            .childOption(ChannelOption.ALLOCATOR, PooledByteBufAllocator.DEFAULT)
            .childHandler(new ChannelInitializer<SocketChannel>() {
                @Override
                protected void initChannel(SocketChannel ch) throws Exception {
                    if (url.getParameter(SSL_ENABLED_KEY, false)) {
                        ch.pipeline().addLast("negotiation", new SslServerTlsHandler(url));
                    }
                    ch.pipeline().addLast("HttpServerCodec", new HttpServerCodec());
                    ch.pipeline().addLast("HttpObjectAggregator", new HttpObjectAggregator(1048576));
                    ch.pipeline().addLast("handler", new HttpServerHandler(restResolver));
                }
            });
    }

    protected void close() throws Throwable {
        try {
            if (channel != null) {
                // unbind.
                channel.close();
            }
        } catch (Throwable e) {
            logger.warn(TRANSPORT_FAILED_CLOSE, "", "", e.getMessage(), e);
        }
        try {
            if (bootstrap != null) {
                long timeout = serverShutdownTimeoutMills;
                long quietPeriod = Math.min(2000L, timeout);
                Future<?> bossGroupShutdownFuture = bossGroup.shutdownGracefully(quietPeriod, timeout, MILLISECONDS);
                Future<?> workerGroupShutdownFuture = workerGroup.shutdownGracefully(quietPeriod, timeout, MILLISECONDS);
                bossGroupShutdownFuture.syncUninterruptibly();
                workerGroupShutdownFuture.syncUninterruptibly();
            }
        } catch (Throwable e) {
            logger.warn(TRANSPORT_FAILED_CLOSE, "", "", e.getMessage(), e);
        }
    }
}
